#!/usr/bin/env python3
"""Check a source manifest and create reproducible, source-only release archives."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
from pathlib import Path
import re
import tarfile
import zipfile

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "SOURCE_SHA256SUMS"
REQUIRED = (
    ".gitattributes", ".gitignore", ".github/workflows/verify.yml",
    "README.md", "STATUS.md", "VERIFICATION.md", "CONTRIBUTING.md",
    "PROVENANCE.md", "CHANGELOG.md", "PomdpLogging.lean", "Audit.lean",
    "AuditCore.lean", "AuditLowerBound.lean", "AuditMain.lean", "AuditMinimax.lean",
    "audit-core.txt", "audit-lower-bound.txt", "audit-main.txt", "audit-minimax.txt",
    "clean-build.log", "check.sh", "setup.sh", "lean-toolchain",
    "lakefile.toml", "lake-manifest.json", "scripts/package.py",
)


def source_paths() -> list[Path]:
    paths = [ROOT / name for name in REQUIRED]
    paths += sorted((ROOT / "PomdpLogging").glob("*.lean"))
    if (ROOT / "LICENSE").is_file():
        paths.append(ROOT / "LICENSE")
    for path in paths:
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f"Missing regular source file: {path.relative_to(ROOT)}")
    return sorted(paths, key=lambda path: path.relative_to(ROOT).as_posix())


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def manifest_text(paths: list[Path]) -> str:
    return "".join(f"{digest(p.read_bytes())}  {p.relative_to(ROOT).as_posix()}\n" for p in paths)


def check(paths: list[Path]) -> None:
    if not MANIFEST.is_file() or MANIFEST.read_text() != manifest_text(paths):
        raise SystemExit("Source manifest mismatch. Review changes, then run: "
                         "python3 scripts/package.py --update")
    print(f"Source manifest verified: {len(paths)} files.")


def build(paths: list[Path]) -> None:
    check(paths)
    match = re.search(r'^version = "([0-9]+\.[0-9]+\.[0-9]+)"$',
                      (ROOT / "lakefile.toml").read_text(), re.MULTILINE)
    if match is None:
        raise SystemExit("Cannot read package version from lakefile.toml")
    stem = f"pomdp-logging-hardness-lean-{match.group(1)}"
    entries = sorted(paths + [MANIFEST], key=lambda p: p.relative_to(ROOT).as_posix())
    dist = ROOT / "dist"
    dist.mkdir(exist_ok=True)
    zip_path = dist / f"{stem}.zip"
    tar_path = dist / f"{stem}.tar.gz"
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in entries:
            name = f"{stem}/{path.relative_to(ROOT).as_posix()}"
            info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            info.create_system = 3
            mode = 0o755 if path.suffix == ".sh" else 0o644
            info.external_attr = (0o100000 | mode) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with tar_path.open("wb") as target:
        with gzip.GzipFile(filename="", mode="wb", fileobj=target, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as archive:
                for path in entries:
                    data = path.read_bytes()
                    info = tarfile.TarInfo(f"{stem}/{path.relative_to(ROOT).as_posix()}")
                    info.size = len(data)
                    info.mode = 0o755 if path.suffix == ".sh" else 0o644
                    info.mtime = 0
                    archive.addfile(info, io.BytesIO(data))
    (dist / "SHA256SUMS").write_text("".join(
        f"{digest(p.read_bytes())}  {p.name}\n" for p in [tar_path, zip_path]))
    print(f"Created {zip_path.name} and {tar_path.name} in dist/.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--update", action="store_true", help="refresh source checksums")
    action.add_argument("--check", action="store_true", help="verify source checksums")
    action.add_argument("--build", action="store_true", help="check and create source archives")
    args = parser.parse_args()
    paths = source_paths()
    if args.update:
        MANIFEST.write_text(manifest_text(paths))
        print(f"Updated SOURCE_SHA256SUMS for {len(paths)} files.")
    elif args.check:
        check(paths)
    else:
        build(paths)


if __name__ == "__main__":
    main()
