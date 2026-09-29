#!/usr/bin/env python3
"""Construct the twelve- or thirteen-symbol word deterministically."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, choices=[12, 13])
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="directory for the word and compact construction recipe")
    args = parser.parse_args()
    tools = Path(__file__).resolve().parent
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((tools.parent / "words/manifest.json").read_text())
    record = next(row for row in manifest["words"] if row["n"] == args.n)
    word = args.output_dir / Path(record["path"]).name
    recipe = args.output_dir / f"superpermutation-{args.n}-recipe.json"
    if word.exists() or recipe.exists():
        parser.error("Output already exists; choose a different directory")
    with tempfile.TemporaryDirectory(prefix="superpermutation-construction-") as temporary:
        executable = Path(temporary) / "construct"
        subprocess.run(["c++", "-O3", "-std=c++17", "-Wall", "-Wextra",
                        str(tools / "construct.cpp"), "-o", str(executable)], check=True)
        subprocess.run([str(executable), str(args.n),
                        str(tools / "construction-input.txt"), str(word), str(recipe),
                        str(tools / "recipes" / f"order-{args.n}.txt")],
                       check=True)
    digest = hashlib.sha256()
    with word.open("rb") as source:
        for chunk in iter(lambda: source.read(4 << 20), b""):
            digest.update(chunk)
    if word.stat().st_size != record["length"] + 1 or digest.hexdigest() != record["sha256"]:
        raise ValueError("Generated word differs from the verified manifest")
    print(f"Word: {word}")
    print(f"Recipe: {recipe}")
    print("Run the independent literal checker before using a newly generated word.")


if __name__ == "__main__":
    main()
