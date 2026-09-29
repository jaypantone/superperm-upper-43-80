#!/usr/bin/env python3
"""Compress an ASCII word as XZ and check its complete decompressed hash."""

import argparse
import hashlib
import json
import lzma
import os
from pathlib import Path
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--degree", type=int, required=True)
    parser.add_argument("--expected-sha256", required=True,
                        help="SHA-256 of the complete input file, including its final LF")
    parser.add_argument("--dictionary-mib", type=int, default=256)
    args = parser.parse_args()
    if not 2 <= args.degree <= 13 or not 1 <= args.dictionary_mib <= 256:
        parser.error("Degree must be 2..13 and dictionary size 1..256 MiB")
    partial = args.output.with_suffix(args.output.suffix + ".partial")
    if args.output.exists() or partial.exists():
        parser.error("Output already exists")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    total = args.source.stat().st_size
    started = last_report = time.monotonic()
    filters = [
        {"id": lzma.FILTER_DELTA, "dist": args.degree},
        {"id": lzma.FILTER_LZMA2, "preset": 9 | lzma.PRESET_EXTREME,
         "dict_size": args.dictionary_mib << 20, "lc": 4, "lp": 0, "pb": 0},
    ]
    compressor = lzma.LZMACompressor(format=lzma.FORMAT_XZ,
                                   check=lzma.CHECK_SHA256, filters=filters)
    digest = hashlib.sha256()
    consumed = 0
    print(json.dumps({"phase": "compressing", "degree": args.degree,
                      "input_bytes": total, "pid": os.getpid()}), flush=True)
    with args.source.open("rb") as source, partial.open("xb") as target:
        for chunk in iter(lambda: source.read(4 << 20), b""):
            digest.update(chunk)
            target.write(compressor.compress(chunk))
            consumed += len(chunk)
            now = time.monotonic()
            if now - last_report >= 30:
                print(json.dumps({"phase": "compressing", "degree": args.degree,
                                  "percent": round(100 * consumed / total, 2),
                                  "seconds": round(now - started, 1)}), flush=True)
                last_report = now
        target.write(compressor.flush())
    del compressor
    if consumed != total or digest.hexdigest() != args.expected_sha256:
        raise ValueError("Input differs from the verified word")
    restored = hashlib.sha256()
    restored_size = 0
    with lzma.open(partial, "rb") as source:
        for chunk in iter(lambda: source.read(4 << 20), b""):
            restored.update(chunk)
            restored_size += len(chunk)
    if restored_size != total or restored.hexdigest() != args.expected_sha256:
        raise ValueError("Decompressed word differs from the verified input")
    packed_hash = hashlib.sha256()
    with partial.open("rb") as source:
        for chunk in iter(lambda: source.read(4 << 20), b""):
            packed_hash.update(chunk)
    if args.output.exists():
        raise FileExistsError(args.output)
    partial.rename(args.output)
    print(json.dumps({"phase": "complete", "degree": args.degree,
                      "input_bytes": total, "file_sha256": restored.hexdigest(),
                      "compressed_bytes": args.output.stat().st_size,
                      "compressed_sha256": packed_hash.hexdigest(),
                      "roundtrip_verified": True,
                      "seconds": round(time.monotonic() - started, 2)}), flush=True)


if __name__ == "__main__":
    main()
