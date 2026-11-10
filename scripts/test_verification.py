"""Regression tests for the link between checked sources, logs and archives."""

import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import zipfile

import package_review
import verify
from verification_snapshot import PDF, SCHEMA_VERSION, hashes, sha256, source_files, write_json


class VerificationProvenance(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Verification fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        (self.root / '.gitignore').write_text('verification/\n')
        (self.root / 'source.py').write_text('print("checked input")\n')
        (self.root / 'requirements.txt').write_text('')
        (self.root / 'paper').mkdir()
        (self.root / PDF).write_bytes(b'fixture PDF')
        self.git('add', '.')
        self.git('commit', '-qm', 'Fixture')
        self.logs = self.root / 'verification'
        self.logs.mkdir()
        self.output = self.logs / 'review-package.zip'
        # A synthetic full run lets us exercise the real packaging path without
        # compiling Lean or relying on installed TeX in these regression tests.
        self.run_id = '20261110T000000Z-' + '0' * 32
        self.run_dir = self.logs / 'runs' / self.run_id
        self.run_dir.mkdir(parents=True)
        required = [name for name, _, _ in verify.PYTHON_CHECKS]
        required += ['latex_1', 'latex_2', 'latex_3', 'lean_build', 'lean_axioms']
        checks = []
        for name in required:
            data = b'fixture successful check\n'
            (self.run_dir / f'{name}.log').write_bytes(data)
            checks.append({'name': name, 'passed': True, 'exit_code': 0,
                           'log_sha256': sha256(data)})
        self.report = {
            'schema_version': SCHEMA_VERSION, 'run_id': self.run_id, 'scope': 'all',
            'status': 'success', 'clean': False, 'checks': checks,
            'inputs': hashes(source_files(self.root)),
            'artifacts': {PDF: sha256((self.root / PDF).read_bytes())},
        }
        self.publish()
        self.quiet = contextlib.ExitStack()
        self.quiet.enter_context(contextlib.redirect_stdout(io.StringIO()))
        self.quiet.enter_context(contextlib.redirect_stderr(io.StringIO()))
        self.addCleanup(self.quiet.close)

    def git(self, *args):
        subprocess.run(['git', *args], cwd=self.root, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def publish(self):
        for name in [self.run_dir / 'summary.json', self.logs / 'all-summary.json',
                     self.logs / 'latest-summary.json']:
            write_json(name, self.report)

    def package(self):
        package_review.package(self.root, self.output)

    def component(self, program):
        # Exercise the real runner, with one short subprocess replacing the
        # expensive mathematical checks. Input capture/reporting are unmocked.
        jobs = [('certificate_guards', '.', ['-c', program])]
        with patch.object(verify, 'ROOT', self.root), patch.object(verify, 'LOGS', self.logs), \
             patch.object(verify, 'PYTHON_CHECKS', jobs), \
             patch.object(sys, 'argv', ['verify.py', '--only', 'python']):
            return verify.main()

    def test_unchanged_payload_and_logs_are_packaged(self):
        self.package()
        with zipfile.ZipFile(self.output) as archive:
            prefix = 'spherical-artin-review/'
            manifest = json.loads(archive.read(prefix + 'REVIEW_PACKAGE.json'))
            self.assertEqual(manifest['verification_run'], self.run_id)
            self.assertFalse(manifest['working_tree_changes'])
            for name, entry in manifest['files'].items():
                self.assertEqual(sha256(archive.read(prefix + name)), entry['sha256'])
        self.assertEqual(self.output.with_suffix('.zip.sha256').read_text().split()[0],
                         sha256(self.output.read_bytes()))

    def test_source_change_rejected_even_when_committed(self):
        (self.root / 'source.py').write_text('print("unchecked input")\n')
        with self.assertRaisesRegex(RuntimeError, 'inputs changed'):
            self.package()
        self.git('add', 'source.py')
        self.git('commit', '-qm', 'Unchecked change')
        with self.assertRaisesRegex(RuntimeError, 'inputs changed'):
            self.package()
        self.assertFalse(self.output.exists())

    def test_dependency_change_rejected(self):
        (self.root / 'requirements.txt').write_text('sympy==0.0\n')
        with self.assertRaisesRegex(RuntimeError, 'inputs changed'):
            self.package()

    def test_added_or_deleted_inputs_rejected(self):
        extra = self.root / 'additional.lean'
        extra.write_text('-- unchecked source\n')
        with self.assertRaisesRegex(RuntimeError, 'inputs changed'):
            self.package()
        extra.unlink()
        (self.root / 'source.py').unlink()
        with self.assertRaisesRegex(RuntimeError, 'inputs changed'):
            self.package()

    def test_pdf_change_rejected(self):
        (self.root / PDF).write_bytes(b'unchecked PDF')
        with self.assertRaisesRegex(RuntimeError, 'PDF changed'):
            self.package()

    def test_log_change_rejected(self):
        (self.run_dir / 'lean_build.log').write_text('FAILED\n')
        with self.assertRaisesRegex(RuntimeError, 'log changed'):
            self.package()

    def test_missing_log_rejected(self):
        (self.run_dir / 'lean_build.log').unlink()
        with self.assertRaises(FileNotFoundError):
            self.package()

    def test_later_failed_component_invalidates_full_run_without_overwriting_logs(self):
        name = self.run_dir / 'certificate_guards.log'
        previous = name.read_bytes()
        self.assertEqual(self.component('raise SystemExit(1)'), 1)
        self.assertEqual(name.read_bytes(), previous)
        latest = json.loads((self.logs / 'latest-summary.json').read_text())
        self.assertEqual(latest['status'], 'failed')
        self.assertNotEqual(latest['run_id'], self.run_id)
        with self.assertRaisesRegex(RuntimeError, 'later verification run'):
            self.package()

    def test_later_successful_component_also_requires_full_verification(self):
        self.assertEqual(self.component('print("ALL CHECKS PASSED")'), 0)
        with self.assertRaisesRegex(RuntimeError, 'later verification run'):
            self.package()

    def test_input_changed_during_successful_check_fails_verification(self):
        program = ('from pathlib import Path; Path("source.py").write_text("changed"); '
                   'print("ALL CHECKS PASSED")')
        self.assertEqual(self.component(program), 1)
        latest = json.loads((self.logs / 'latest-summary.json').read_text())
        self.assertEqual(latest['status'], 'failed')
        self.assertIn('inputs changed', latest['error'])

    def test_incomplete_or_failed_full_summary_rejected(self):
        self.report['checks'].pop()
        self.publish()
        with self.assertRaisesRegex(RuntimeError, 'successfully before packaging'):
            self.package()

    def test_full_summary_must_match_run_record(self):
        (self.run_dir / 'summary.json').write_text('{}')
        with self.assertRaisesRegex(RuntimeError, 'differs from its run record'):
            self.package()

    def test_source_change_during_packaging_preserves_previous_archive(self):
        self.package()
        old = self.output.read_bytes()
        original = zipfile.ZipFile.writestr
        def mutate(archive, *args, **kwargs):
            (self.root / 'source.py').write_text('changed during packaging')
            return original(archive, *args, **kwargs)
        with patch.object(zipfile.ZipFile, 'writestr', mutate), \
             self.assertRaisesRegex(RuntimeError, 'inputs changed'):
            self.package()
        self.assertEqual(self.output.read_bytes(), old)


if __name__ == '__main__':
    result = unittest.main(exit=False).result
    if not result.wasSuccessful():
        sys.exit(1)
    print('ALL CHECKS PASSED')
