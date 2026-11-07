#!/usr/bin/env python3
"""Package the current source tree, PDF and successful verification logs for review."""

import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

from verify import PYTHON_CHECKS

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "verification/review-package.zip"


def main():
    summary_path = ROOT / "verification/all-summary.json"
    summary = json.loads(summary_path.read_text())
    required = {name for name, _, _ in PYTHON_CHECKS} | {
        "latex_1", "latex_2", "latex_3", "lean_build", "lean_axioms"}
    checks = summary.get("checks", [])
    if ("error" in summary or not required <= {c["name"] for c in checks}
            or not all(c["passed"] and c["exit_code"] == 0 for c in checks)):
        raise SystemExit("Run scripts/verify.py successfully before packaging.")

    # Use working-tree contents, including new source files, rather than HEAD.
    listed = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT)
    paths = {Path(name) for name in listed.decode().split("\0") if name}
    paths = {p for p in paths if (ROOT / p).is_file() and p.parts[0] != "verification"}
    paths.add(Path("verification/all-summary.json"))
    paths.update(Path("verification") / f"{c['name']}.log" for c in checks)
    contents = {p.as_posix(): (ROOT / p).read_bytes() for p in sorted(paths)}
    manifest = {
        "description": "Current working-tree source snapshot with verification logs; dependencies are installed separately.",
        "base_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "working_tree_changes": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
        "files": {name: {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
                  for name, data in contents.items()},
    }
    prefix = "spherical-artin-review/"
    with zipfile.ZipFile(OUTPUT, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, data in contents.items():
            archive.writestr(prefix + name, data)
        archive.writestr(prefix + "REVIEW_PACKAGE.json", json.dumps(manifest, indent=2) + "\n")
    with zipfile.ZipFile(OUTPUT) as archive:
        if archive.testzip() is not None:
            raise RuntimeError("Archive integrity check failed")
        for name, metadata in manifest["files"].items():
            if hashlib.sha256(archive.read(prefix + name)).hexdigest() != metadata["sha256"]:
                raise RuntimeError(f"Archive checksum mismatch: {name}")
    print(f"Verified {len(contents)} files: {OUTPUT} ({OUTPUT.stat().st_size:,} bytes)")


if __name__ == "__main__":
    main()
