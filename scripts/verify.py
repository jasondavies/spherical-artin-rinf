#!/usr/bin/env python3
"""Run the paper's certificates, LaTeX build and conditional Lean proofs."""

import argparse
import importlib.metadata
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid

from verification_snapshot import (
    PDF, SCHEMA_VERSION, check_inputs, hashes, sha256, source_files,
    verification_lock, write_json,
)

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / "verification"
PYTHON_CHECKS = [
    ("certificate_guards", "code", ["test_certificate_guards.py"]),
    ("verification_provenance", "scripts", ["test_verification.py"]),
    ("explicit_constituents", "code/indep", ["explicit_constituents.py"]),
    ("exceptional_srg", "code/indep", ["exceptional_srg.py"]),
    ("holonomy", "code/indep", ["out_check.py", "H3", "F4", "H4", "E6", "E7"]),
    ("holonomy_stabilisers", "code/indep", ["out_check_stab.py", "E7", "E8"]),
    ("dihedral", "code/indep", ["dihedral_quotient.py"]),
    ("dihedral_lean_export", "lean/scripts", ["export_dihedral5.py", "--check"]),
    ("quotient_families", "code/indep", ["quotient_families.py", "--max-m", "46"]),
    ("characters", "code/indep", ["indep_check.py", "H3", "F4", "H4", "D5", "E6", "E7"]),
    ("commutants", "code/indep", ["indep_check.py", "commutant:E8", "commutant:H3", "commutant:F4"]),
    ("scalar_certificates", "code", ["certify.py", "H3", "F4", "H4", "E6", "E7", "E8", "D5"]),
    ("outer_witnesses", "code", ["certify_outer.py", "H3", "F4", "H4"]),
]

REQUIRED_AXIOM_REPORTS = {
    *(f"ArtinRinf.{name}.artin_{name}_R_infty_FH" for name in
      ["D5", "E6", "E7", "E8", "F4", "H3", "H4"]),
    "ArtinRinf.Dihedral5.Presentation.toGamma_kernel",
    "ArtinRinf.Dihedral5.Presentation.artinQuotient_exists_reidemeister_eighteen",
    "ArtinRinf.Dihedral5.Presentation.artinQuotient_not_R_infty",
}


def validate_axiom_report(output):
    """Check named theorem coverage and axioms, including Lean's wrapped lists."""
    reports = dict(re.findall(r"'([^\n]+)' depends on axioms: \[([^\]]*)\]", output))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if (len(reports) < 20 or not REQUIRED_AXIOM_REPORTS <= reports.keys()
            or any({name.strip() for name in axioms.split(",") if name.strip()} - allowed
                   for axioms in reports.values())):
        raise RuntimeError("Unexpected or missing axiom report")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", choices=["python", "paper", "lean"], help="run one component")
    parser.add_argument("--clean", action="store_true", help="remove local paper/Lean build outputs first; retain Mathlib cache")
    parser.add_argument("--threads", type=int, default=4, help="Lean worker count (default: 4)")
    args = parser.parse_args()
    if args.threads < 1:
        parser.error("--threads must be positive")
    try:
        with verification_lock(ROOT):
            return verify(args)
    except (OSError, RuntimeError) as error:
        print(error, file=sys.stderr)
        return 1


def verify(args):
    scope = args.only or "all"
    run_id = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()) + "-" + uuid.uuid4().hex
    run_dir = LOGS / "runs" / run_id
    run_dir.mkdir(parents=True)
    report = {"schema_version": SCHEMA_VERSION, "run_id": run_id, "scope": scope,
              "status": "running", "python": sys.version, "clean": args.clean,
              "started_at": time.time(), "checks": []}
    # Invalidate packaging immediately, including if the run is interrupted.
    write_json(LOGS / "latest-summary.json", report)
    env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1",
               LEAN_NUM_THREADS=str(args.threads), PYTHONDONTWRITEBYTECODE="1")
    # The certificate scripts use assertions: never inherit Python's -O setting.
    env.pop("PYTHONOPTIMIZE", None)

    def run(name, command, cwd=ROOT, marker=None):
        print(f"Running {name} ...", flush=True)
        start = time.monotonic()
        log = run_dir / f"{name}.log"
        with log.open("w") as out:
            result = subprocess.run(command, cwd=cwd, env=env, stdout=out, stderr=subprocess.STDOUT)
        content = log.read_text(errors="replace")
        ok = result.returncode == 0 and (marker is None or marker in content)
        report["checks"].append({"name": name, "command": command, "cwd": str(cwd.relative_to(ROOT)),
                                 "seconds": round(time.monotonic() - start, 2), "passed": ok,
                                 "exit_code": result.returncode,
                                 "log_sha256": sha256(log.read_bytes())})
        if not ok:
            raise RuntimeError(f"{name} failed; see {log}\n{content[-3000:]}")
        print(f"  PASS ({report['checks'][-1]['seconds']}s)", flush=True)
        return content

    try:
        report["inputs"] = hashes(source_files(ROOT))
        if args.only in (None, "python"):
            report["dependencies"] = {}
            for line in (ROOT / "requirements.txt").read_text().splitlines():
                name, expected = line.split("==")
                actual = importlib.metadata.version(name)
                report["dependencies"][name] = actual
                if actual != expected:
                    raise RuntimeError(f"{name} {actual}: install requirements.txt (expected {expected})")
            for name, directory, command in PYTHON_CHECKS:
                run(name, [sys.executable, *command], ROOT / directory, "ALL CHECKS PASSED")
        if args.only in (None, "paper"):
            if args.clean:
                for suffix in ["aux", "log", "out", "toc", "fls", "fdb_latexmk", "pdf"]:
                    (ROOT / "paper" / f"spherical-artin-rinf.{suffix}").unlink(missing_ok=True)
            for i in range(1, 4):
                run(f"latex_{i}", ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "spherical-artin-rinf.tex"], ROOT / "paper")
            latex_log = (ROOT / "paper/spherical-artin-rinf.log").read_text()
            if re.search(r"undefined|multiply defined|Rerun to get|Overfull \\[hv]box", latex_log):
                raise RuntimeError("Unresolved LaTeX references or overfull boxes; see paper/spherical-artin-rinf.log")
        if args.only in (None, "lean"):
            lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
            if args.clean:
                # Bare `lake clean` also cleans dependency packages: name this package explicitly.
                run("lean_clean", [lake, "clean", "artin_rinf"], ROOT / "lean")
            run("lean_build", [lake, "build"], ROOT / "lean", "Build completed successfully")
            axioms = run("lean_axioms", [lake, "env", "lean", "scripts/print_axioms.lean"], ROOT / "lean")
            validate_axiom_report(axioms)
        if args.only in (None, "paper"):
            report["artifacts"] = {PDF: sha256((ROOT / PDF).read_bytes())}
    except (OSError, RuntimeError, importlib.metadata.PackageNotFoundError) as error:
        report["error"] = str(error)
        print(error, file=sys.stderr)
    finally:
        if "inputs" in report:
            try:
                check_inputs(ROOT, report["inputs"])
            except (OSError, RuntimeError) as error:
                report["error"] = str(error)
                print(error, file=sys.stderr)
        # A run is successful only after every required operation finishes.
        # KeyboardInterrupt and other uncaught exceptions must not publish success.
        report["status"] = "success" if "error" not in report and sys.exc_info()[0] is None else "failed"
        report["finished_at"] = time.time()
        write_json(run_dir / "summary.json", report)
        write_json(LOGS / f"{scope}-summary.json", report)
        write_json(LOGS / "latest-summary.json", report)
    if "error" in report:
        return 1
    print(f"ALL CHECKS PASSED; logs and summary: {run_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
