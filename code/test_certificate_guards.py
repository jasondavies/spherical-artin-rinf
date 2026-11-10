"""Fault-injection checks: incomplete certificate data must never pass."""

import contextlib
import io
from pathlib import Path
import runpy
import subprocess
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import numpy as np
from sympy import Matrix

sys.path.insert(0, str(Path(__file__).resolve().parent / 'indep'))
import certify
import certify_outer
import indep_check
import exceptional_srg
import permgroup
import uniform_check


class CertificateGuards(unittest.TestCase):
    def setUp(self):
        self.output = contextlib.redirect_stdout(io.StringIO())
        self.output.__enter__()
        self.addCleanup(self.output.__exit__, None, None, None)

    def test_missing_exact_constituent(self):
        fake = SimpleNamespace(N=2, n=1, rp=[np.array([1, 0])])
        with patch.object(certify, 'Cox', return_value=fake), \
             patch.object(certify, 'orbitals', return_value=(np.zeros((2, 2)), 1)), \
             patch.object(certify, 'certify_constituent', return_value=[]):
            with self.assertRaisesRegex(ValueError, 'missing or duplicate'):
                certify.main('H3', [4])

    def test_f4_requires_both_constituents(self):
        fake = SimpleNamespace(N=2, n=1, rp=[np.array([1, 0])])
        with patch.object(certify, 'Cox', return_value=fake), \
             patch.object(certify, 'orbitals', return_value=(np.zeros((2, 2)), 1)), \
             patch.object(certify, 'certify_constituent', return_value=[(0, 2, True, Matrix.eye(2))]):
            with self.assertRaisesRegex(ValueError, 'missing or duplicate'):
                certify.main('F4', [2])

    def test_outer_rejects_missing_and_partial_data(self):
        good = [np.zeros((15, 4))]
        for constituents, witnesses in [([], []), (good, []), (good, [('stable', 0, 1, 0)]),
                                       (good, [('stable', 0, 1, 0)] * 2)]:
            with self.subTest(witnesses=witnesses), self.assertRaises(ValueError):
                certify_outer.validate_coverage('H3', constituents, witnesses)
        # Exercise the actual checker entry point, not just the validation helper.
        with patch.object(certify_outer, 'outer_check', return_value=(None, None, [], {'wit': []})):
            with self.assertRaises(ValueError):
                certify_outer.verify('H3')

    def test_valid_outer_coverage(self):
        good = [np.zeros((24, 2)), np.zeros((24, 2))]
        witnesses = [('swap', a, eps, 0) for a in (0, 1) for eps in (1, -1)]
        certify_outer.validate_coverage('F4', good, witnesses)

    def test_commutant_rejects_empty_or_trivial_only_spectrum(self):
        for spectrum in (np.array([]), np.array([120])):
            with self.subTest(spectrum=spectrum), patch.object(indep_check, 'FAIL', []), \
                 patch.object(indep_check.np.linalg, 'eigvalsh', return_value=spectrum):
                indep_check.commutant_check('E8')
                self.assertTrue(indep_check.FAIL)
                self.assertIn('missing or incorrect', indep_check.FAIL[0])

    def test_independent_outer_rejects_empty_constituents(self):
        with patch.object(indep_check, 'FAIL', []):
            indep_check.outer_witnesses('H3', None, None, None, [], None)
            self.assertEqual(indep_check.FAIL, ['H3: missing outer-case constituents'])

    def test_uniform_positive_requires_constituents_and_automorphisms(self):
        witness = [(True, True, ('(i)', 4))]
        for results, good in [([], []), ([], [4]), (witness, [])]:
            self.assertFalse(uniform_check.positive_criterion_holds(
                {'results': results, 'good': good, 'clash': []}))
        self.assertTrue(uniform_check.positive_criterion_holds(
            {'results': witness, 'good': [4], 'clash': []}))

    def test_srg_identity_failure_reaches_exit_status(self):
        output = io.StringIO()
        with patch.object(exceptional_srg, 'FAIL', []), \
             patch.object(exceptional_srg.np, 'array_equal', return_value=False), \
             contextlib.redirect_stdout(output):
            self.assertEqual(exceptional_srg.main(), 1)
            self.assertEqual(exceptional_srg.FAIL,
                             [name + ' SRG/orbitals/spectrum' for name in ('E6', 'E7', 'E8')])
        self.assertNotIn('ALL CHECKS PASSED', output.getvalue())

    def test_srg_rejects_corrupt_eigenbases(self):
        original = exceptional_srg.intbasis

        def corrupt_basis(M):
            K = original(M)
            if corruption == 'constant':
                K[:, 0] = 1
            elif corruption == 'duplicate':
                K[:, 0] = K[:, 1]
            elif corruption == 'empty':
                K = K[:, :0]
            return K

        for corruption, failures in [
            ('constant', ['eigenbasis identities', 'constant-vector orthogonality']),
            ('duplicate', ['complete independent eigenbases']),
            ('empty', ['complete independent eigenbases', 'nontrivial simple-reflection actions']),
        ]:
            with self.subTest(corruption=corruption), \
                 patch.object(exceptional_srg, 'FAIL', []), \
                 patch.object(exceptional_srg, 'intbasis', side_effect=corrupt_basis):
                exceptional_srg.analyse('E6', 6, '3^15 (-3)^20')
                for failure in failures:
                    self.assertIn('E6 ' + failure, exceptional_srg.FAIL)

    def test_holonomy_rejects_nontrivial_centre_at_entry_point(self):
        script = Path(__file__).resolve().parent / 'indep/out_check.py'
        output = io.StringIO()
        with patch.object(permgroup, 'centre', return_value=[0, 1]), \
             patch.object(sys, 'argv', [str(script), 'H3']), \
             contextlib.redirect_stdout(output):
            with self.assertRaises(SystemExit) as error:
                runpy.run_path(str(script), run_name='__main__')
        self.assertEqual(error.exception.code, 1)
        self.assertIn('H3: nontrivial centre', output.getvalue())
        self.assertNotIn('ALL CHECKS PASSED', output.getvalue())

    def test_empty_command_lines_fail(self):
        root = Path(__file__).resolve().parent
        for script in ['certify.py', 'certify_outer.py', 'indep/indep_check.py',
                       'indep/out_check.py', 'indep/out_check_stab.py', 'indep/uniform_check.py']:
            with self.subTest(script=script):
                result = subprocess.run([sys.executable, str(root / script)], capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn('ALL CHECKS PASSED', result.stdout)


if __name__ == '__main__':
    result = unittest.main(exit=False).result
    if not result.wasSuccessful():
        sys.exit(1)
    print('ALL CHECKS PASSED')
