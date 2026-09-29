#!/usr/bin/env python3
"""Check literal coverage and manifest hashes; optionally test all deletions."""

import argparse
import gzip
import hashlib
import json
import lzma
from math import factorial
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            result.update(chunk)
    return result.hexdigest()


def verify_file(path, row, checker, deletions):
    require(path.stat().st_size == row["length"] + 1,
            f"{path.name}: incorrect byte length")
    file_hash = hashlib.sha256()
    word_hash = hashlib.sha256()
    remaining = row["length"]
    with path.open("rb") as stream:
        while remaining:
            chunk = stream.read(min(remaining, 1 << 20))
            require(bool(chunk), f"{path.name}: unexpected end of file")
            file_hash.update(chunk)
            word_hash.update(chunk)
            remaining -= len(chunk)
        ending = stream.read()
        require(ending == b"\n", f"{path.name}: expected exactly one final LF")
        file_hash.update(ending)
    require(file_hash.hexdigest() == row["sha256"],
            f"{path.name}: file hash mismatch")
    require(word_hash.hexdigest() == row["word_sha256"],
            f"{path.name}: word hash mismatch")
    command = [str(checker), str(row["n"]), row["alphabet"], str(path)]
    if deletions:
        command.append("--deletions")
    report = json.loads(subprocess.check_output(command, text=True))
    required = factorial(row["n"])
    require(report["n"] == row["n"] and report["alphabet"] == row["alphabet"]
            and report["length"] == row["length"]
            and report["required_permutations"] == required
            and report["distinct_permutations"] == required
            and report["missing_permutations"] == 0
            and report["extra_occurrences"] == row["extra_permutation_occurrences"],
            f"{path.name}: literal scan disagrees with manifest")
    if deletions:
        require(report["tested_deletions"] == row["length"]
                and not report["coverage_preserving_deletions"],
                f"{path.name}: at least one character can be deleted")
    print(json.dumps(report), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deletions", action="store_true",
                        help="also exhaustively test single-character deletions")
    parser.add_argument("--degrees", type=int, nargs="+", default=[8, 9, 10, 11],
                        help="alphabet sizes to check (default: 8 through 11)")
    parser.add_argument("--large-dir", type=Path,
                        help="alternative directory containing large text, XZ, or gzip files")
    parser.add_argument("--checker", type=Path,
                        help="use an already compiled literal_check executable")
    args = parser.parse_args()
    rows = json.loads((ROOT / "words/manifest.json").read_text())["words"]
    by_degree = {}
    for row in rows:
        by_degree.setdefault(row["n"], []).append(row)
    require(all(n in by_degree for n in args.degrees),
            "Requested degree has no word in the manifest")
    with tempfile.TemporaryDirectory(prefix="superpermutation-check-") as temporary:
        scratch = Path(temporary)
        checker = args.checker.resolve() if args.checker else scratch / "literal_check"
        if args.checker is None:
            subprocess.run(["c++", "-O3", "-std=c++17", "-Wall", "-Wextra",
                            str(ROOT / "tools/literal_check.cpp"), "-o", str(checker)],
                           check=True)
        subprocess.run([str(checker), "--self-test"], check=True)
        for row in (row for n in sorted(set(args.degrees)) for row in by_degree[n]):
            path = ROOT / row["path"]
            extracted = None
            if not path.is_file():
                compressed = ROOT / row.get("compressed_path", "missing")
                if args.large_dir:
                    path = args.large_dir / Path(row["path"]).name
                    if "compressed_filename" in row:
                        compressed = args.large_dir / row["compressed_filename"]
                if not path.is_file() and compressed.is_file():
                    require(digest(compressed) == row["compressed_sha256"],
                            f"{compressed.name}: compressed hash mismatch")
                    extracted = scratch / Path(row["path"]).name
                    opener = lzma.open if compressed.suffix == ".xz" else gzip.open
                    with opener(compressed, "rb") as source, extracted.open("wb") as target:
                        shutil.copyfileobj(source, target, length=1 << 20)
                    path = extracted
            require(path.is_file(), f"Missing word: {row['path']}; supply --large-dir for release assets")
            verify_file(path, row, checker, args.deletions)
            if extracted:
                extracted.unlink()


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"Verification failed: {error}")
