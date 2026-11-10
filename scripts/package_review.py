#!/usr/bin/env python3
"""Package only the source, PDF and logs bound to a successful full verification."""

import json
from pathlib import Path
import re
import subprocess
import sys
import zipfile

from verify import PYTHON_CHECKS
from verification_snapshot import (
    PDF, SCHEMA_VERSION, check_inputs, hashes, sha256, verification_lock,
)

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "verification/review-package.zip"


def verified_contents(root):
    """Read once, then validate the bytes that will actually enter the ZIP."""
    summary_bytes = (root / "verification/all-summary.json").read_bytes()
    summary = json.loads(summary_bytes)
    if (root / "verification/latest-summary.json").read_bytes() != summary_bytes:
        raise RuntimeError("A later verification run exists; run the full workflow before packaging")
    run_id = summary.get("run_id", "")
    if not re.fullmatch(r"\d{8}T\d{6}Z-[0-9a-f]{32}", run_id):
        raise RuntimeError("Missing or invalid verification run identifier; rerun the full workflow")
    run_path = Path("verification/runs") / run_id
    if (root / run_path / "summary.json").read_bytes() != summary_bytes:
        raise RuntimeError("Full verification summary differs from its run record")
    required = {name for name, _, _ in PYTHON_CHECKS} | {
        "latex_1", "latex_2", "latex_3", "lean_build", "lean_axioms"}
    if summary.get("clean"):
        required.add("lean_clean")
    checks = summary.get("checks", [])
    if (summary.get("schema_version") != SCHEMA_VERSION or summary.get("scope") != "all"
            or summary.get("status") != "success" or "error" in summary
            or len(checks) != len(required) or {c["name"] for c in checks} != required
            or not all(c["passed"] and c["exit_code"] == 0 for c in checks)):
        raise RuntimeError("Run scripts/verify.py successfully before packaging")
    expected = summary.get("inputs")
    if not isinstance(expected, dict) or not expected:
        raise RuntimeError("Verification report has no input hashes; rerun the full workflow")
    contents = check_inputs(root, expected)
    artifacts = summary.get("artifacts", {})
    if set(artifacts) != {PDF}:
        raise RuntimeError("Verification report has no checked PDF")
    pdf = (root / PDF).read_bytes()
    if sha256(pdf) != artifacts[PDF]:
        raise RuntimeError("Generated PDF changed after verification")
    contents[PDF] = pdf
    contents["verification/all-summary.json"] = summary_bytes
    contents[(run_path / "summary.json").as_posix()] = summary_bytes
    for check in checks:
        name = (run_path / f"{check['name']}.log").as_posix()
        log = (root / name).read_bytes()
        if sha256(log) != check.get("log_sha256"):
            raise RuntimeError(f"Verification log changed: {name}")
        contents[name] = log
    return contents, summary


def package(root, output):
    with verification_lock(root):
        contents, summary = verified_contents(root)
        # This identifies the full submitted payload independently of a code pin.
        snapshot = {name: digest for name, digest in hashes(contents).items()
                    if not name.startswith("verification/")}
        manifest = {
            "description": "Source and PDF snapshot bound to the included successful verification run.",
            "verification_run": summary["run_id"],
            "snapshot_sha256": sha256(json.dumps(snapshot, sort_keys=True).encode()),
            "base_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
            "working_tree_changes": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=root)),
            "files": {name: {"sha256": sha256(data), "bytes": len(data)}
                      for name, data in sorted(contents.items())},
        }
        prefix = "spherical-artin-review/"
        temporary = output.with_suffix(".tmp")
        try:
            with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED) as archive:
                for name, data in sorted(contents.items()):
                    archive.writestr(prefix + name, data)
                archive.writestr(prefix + "REVIEW_PACKAGE.json", json.dumps(manifest, indent=2) + "\n")
            with zipfile.ZipFile(temporary) as archive:
                if archive.testzip() is not None:
                    raise RuntimeError("Archive integrity check failed")
                for name, metadata in manifest["files"].items():
                    if sha256(archive.read(prefix + name)) != metadata["sha256"]:
                        raise RuntimeError(f"Archive checksum mismatch: {name}")
            # Reject edits made while the archive was being assembled as well.
            check_inputs(root, summary["inputs"])
            if sha256((root / PDF).read_bytes()) != summary["artifacts"][PDF]:
                raise RuntimeError("Generated PDF changed during packaging")
            temporary.replace(output)
        finally:
            temporary.unlink(missing_ok=True)
        digest = sha256(output.read_bytes())
        output.with_suffix(".zip.sha256").write_text(f"{digest}  {output.name}\n")
        print(f"Verified {len(contents)} files: {output} ({output.stat().st_size:,} bytes)")
        print(f"Archive SHA-256: {digest}")


def main():
    try:
        package(ROOT, OUTPUT)
    except (OSError, RuntimeError, ValueError, KeyError) as error:
        print(f"Packaging refused: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
