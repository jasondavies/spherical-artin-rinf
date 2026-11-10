"""Source snapshots and exclusive access shared by verification and packaging."""

from contextlib import contextmanager
import fcntl
import hashlib
import json
from pathlib import Path
import subprocess

PDF = "paper/spherical-artin-rinf.pdf"
SCHEMA_VERSION = 1


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def source_files(root):
    """Read the exact repository payload, excluding build outputs and the PDF."""
    listed = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=root)
    names = sorted(set(listed.decode().split("\0")) - {"", PDF})
    files = {}
    for name in names:
        path = Path(name)
        if path.parts[0] == "verification":
            continue
        if path.is_absolute() or ".." in path.parts:
            raise RuntimeError(f"Invalid repository path: {name}")
        full = root / path
        if full.is_symlink():
            raise RuntimeError(f"Source snapshot does not support symlinks: {name}")
        if full.is_file():
            files[name] = full.read_bytes()
    return files


def hashes(files):
    return {name: sha256(data) for name, data in sorted(files.items())}


def check_inputs(root, expected):
    files = source_files(root)
    actual = hashes(files)
    if actual != expected:
        changed = sorted(name for name in actual.keys() | expected.keys()
                         if actual.get(name) != expected.get(name))
        raise RuntimeError("Verification inputs changed: " + ", ".join(changed))
    return files


def write_json(path, value):
    """Publish a complete report atomically."""
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


@contextmanager
def verification_lock(root):
    directory = root / "verification"
    directory.mkdir(exist_ok=True)
    with (directory / ".lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError("Another verification or packaging process is running") from error
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)
