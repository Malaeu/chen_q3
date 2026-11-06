#!/usr/bin/env python3
"""Build and run the Round 8 Part 2 C++ scan under ``uv run``.

No Python package dependencies are used. Native MPFR/GMP/zlib are linked by
the system compiler so the sign intervals use directed MPFR rounding.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import shlex
import subprocess
import sys
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
CPP = HERE / "core_scan.cpp"
OUT_DEFAULT = HERE
BIN = Path("/tmp/q3_r8_core_scan")
LOG_DEFAULT = HERE / "core_run.log"


def capture(command: list[str]) -> str:
    try:
        return subprocess.run(command, check=True, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT).stdout.strip()
    except Exception as exc:  # metadata is useful even when one probe is absent
        return f"UNAVAILABLE: {type(exc).__name__}: {exc}"


def build() -> list[str]:
    compiler = os.environ.get("CXX", "clang++")
    command = [compiler, "-std=c++17", "-O3", "-DNDEBUG", str(CPP), "-o", str(BIN),
               "-I/opt/homebrew/include", "-L/opt/homebrew/lib", "-lmpfr", "-lgmp", "-lz"]
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"native build failed ({result.returncode}):\n{result.stdout}")
    return command


def stream_run(command: list[str], log: Path) -> tuple[int, float]:
    start = time.monotonic()
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("w", encoding="ascii", newline="\n") as f:
        f.write("COMMAND: " + shlex.join(command) + "\n")
        f.flush()
        proc = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, encoding="utf-8", errors="replace", bufsize=1)
        assert proc.stdout is not None
        for line in proc.stdout:
            print(line, end="", flush=True)
            f.write(line)
            f.flush()
        code = proc.wait()
    return code, time.monotonic() - start


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="mode", required=True)
    for name in ("scan", "full", "bench"):
        p = sub.add_parser(name)
        p.add_argument("--out", type=Path, default=OUT_DEFAULT)
        p.add_argument("--log", type=Path, default=LOG_DEFAULT)
        if name == "scan":
            p.add_argument("--max", type=int, default=10_000_000)
            p.add_argument("--bits", type=int, default=192)
        elif name == "full":
            p.add_argument("--crossings", type=Path, default=HERE / "core_crossings.csv")
            p.add_argument("--max", type=int, default=10_000)
        else:
            p.add_argument("--N", type=int, default=10_000)
            p.add_argument("--samples", type=int, default=20_000)
    ns = ap.parse_args()
    build_command = build()
    if ns.mode == "scan":
        command = [str(BIN), "scan", str(ns.out), str(ns.max), str(ns.bits)]
    elif ns.mode == "full":
        command = [str(BIN), "full", str(ns.out), str(ns.crossings), str(ns.max)]
    else:
        command = [str(BIN), "bench", str(ns.out), str(ns.N), str(ns.samples)]
    code, elapsed = stream_run(command, ns.log)
    meta = {
        "mode": ns.mode,
        "command": command,
        "build_command": build_command,
        "python": sys.version,
        "uv": capture(["uv", "--version"]),
        "compiler": capture([build_command[0], "--version"]).splitlines()[:2],
        "platform": platform.platform(),
        "native_source_sha256": hashlib.sha256(CPP.read_bytes()).hexdigest(),
        "elapsed_seconds": elapsed,
        "exit_code": code,
        "log": str(ns.log),
        "note": "Head/full-core values use long double; only b_N sign classifications use directed MPFR intervals.",
    }
    (ns.out / ("core_runner_metadata_" + ns.mode + ".json")).write_text(
        json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
