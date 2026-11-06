#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Compile, brute-check, then run the preregistered true integer systems.

Run from any directory with:
    uv run --script scripts/run_true.py --full
The C++ binary is temporary and is never written into the result folder.
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

EXPECTED_HEAD = "8e2e29a866600c16cf38127ff5325ac97dc2880e"
EXPECTED_GRID_ROWS = 701
EXPECTED_SAMPLE_ROWS = 8000
EXPECTED_DECADE_ROWS = 9
SEEDS = (4401, 4402, 4403, 4404, 4405)
STREAMS = ("S0", *(f"S4_seed{seed}" for seed in SEEDS), "S5")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def write_json(path: Path, obj: object) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def tee_command(command: list[str], cwd: Path, log, announce: str) -> tuple[int, float]:
    print(announce, flush=True)
    log.write(announce + "\n")
    log.flush()
    start = time.monotonic()
    process = subprocess.Popen(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    assert process.stdout is not None
    for line in process.stdout:
        print(line, end="", flush=True)
        log.write(line)
        log.flush()
    return_code = process.wait()
    elapsed = time.monotonic() - start
    timing = f"COMMAND_DONE exit={return_code} elapsed_s={elapsed:.3f}"
    print(timing, flush=True)
    log.write(timing + "\n")
    log.flush()
    return return_code, elapsed


def csv_rows(path: Path) -> tuple[list[str], int]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle)
        header = next(reader)
        return header, sum(1 for _ in reader)


def main() -> int:
    script = Path(__file__).resolve()
    result_dir = script.parent.parent
    repo = script.parents[5]
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-directory", type=Path, default=result_dir)
    parser.add_argument("--full", action="store_true", help="run all registered limits (the default)")
    parser.add_argument("--self-test-only", action="store_true", help="run build and small brute checks only")
    args = parser.parse_args()
    output_dir = args.output_directory.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    source = script.with_name("true_systems.cpp")
    prereg_source = result_dir / "PREREGISTRATION.json"
    prereg_relative = "docs/routeB_bus/diag/PRIME_PROPERTY_ABLATION_2026-11-06/PREREGISTRATION.json"
    log_path = output_dir / "true_systems.log"
    run_json_path = output_dir / "true_systems_run.json"
    checks_path = output_dir / "true_systems_checks.json"

    metadata: dict[str, object] = {
        "status": "RUNNING",
        "classification": "FINITE_DIAGNOSTIC_NOT_RH",
        "started_utc": utc_now(),
        "repo": str(repo),
        "head": None,
        "pre_run_commit": EXPECTED_HEAD,
        "preregistration_sha256": None,
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "output_directory": str(output_dir),
        "limits": {"S0": 100000000, "S4_each_seed": 100000000, "S5": 100000000},
        "S4_seeds": list(SEEDS),
        "commands": [],
        "elapsed_seconds": {},
        "postflight": {},
        "truncations": [
            "Liouville first positive at 906150258 is above the registered 100000000 limit and was not run.",
            "J4 planted output ends at 10000000, the full registered slope-check endpoint; baseline S0 continues to 100000000.",
        ],
    }
    failure: str | None = None

    with log_path.open("w", encoding="utf-8") as log:
        try:
            head = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=repo, text=True
            ).strip()
            metadata["head"] = head
            ancestor = subprocess.run(
                ["git", "merge-base", "--is-ancestor", EXPECTED_HEAD, head], cwd=repo
            )
            if ancestor.returncode != 0:
                raise RuntimeError(
                    f"preregistration commit is not an ancestor of HEAD: {EXPECTED_HEAD} vs {head}"
                )
            prereg_bytes = prereg_source.read_bytes()
            committed_prereg_bytes = subprocess.check_output(
                ["git", "show", f"{EXPECTED_HEAD}:{prereg_relative}"], cwd=repo
            )
            if prereg_bytes != committed_prereg_bytes:
                raise RuntimeError("local preregistration bytes differ from the pinned pre-run commit")
            prereg_data = json.loads(prereg_bytes.decode("utf-8"))
            if prereg_data.get("status") != "PRE_RUN":
                raise RuntimeError("preregistration is not marked PRE_RUN")
            metadata["preregistration_sha256"] = hashlib.sha256(prereg_bytes).hexdigest()
            metadata["preregistration_commit"] = EXPECTED_HEAD
            metadata["preregistration_blob"] = subprocess.check_output(
                ["git", "rev-parse", f"{EXPECTED_HEAD}:{prereg_relative}"], cwd=repo, text=True
            ).strip()
            wrapper_command = [
                "uv", "run", "--script", str(script), "--full",
                "--output-directory", str(output_dir),
            ]
            metadata["wrapper_command"] = wrapper_command

            compiler = shutil.which("g++")
            if compiler is None:
                raise RuntimeError("g++ was not found")
            compiler_version = subprocess.check_output(
                [compiler, "--version"], cwd=repo, text=True
            ).splitlines()[0]
            metadata["compiler"] = compiler
            metadata["compiler_version"] = compiler_version
            binary = Path(tempfile.gettempdir()) / f"q3_true_systems_{os.getpid()}"
            compile_command = [
                compiler, "-O3", "-std=c++17", "-Wall", "-Wextra", "-pedantic",
                str(source), "-o", str(binary),
            ]
            metadata["commands"].append(compile_command)
            code, seconds = tee_command(
                compile_command, repo, log,
                "PHASE compile start flags=-O3,-std=c++17,no-fast-math",
            )
            metadata["elapsed_seconds"]["compile"] = seconds
            if code != 0:
                raise RuntimeError(f"C++ compile failed with exit {code}")

            self_command = [str(binary), "--self-test"]
            metadata["commands"].append(self_command)
            code, seconds = tee_command(
                self_command, repo, log, "PHASE small_brute_checks start"
            )
            metadata["elapsed_seconds"]["self_test"] = seconds
            if code != 0:
                raise RuntimeError(f"small brute checks failed with exit {code}")
            metadata["self_tests"] = {
                "status": "PASS",
                "command": self_command,
                "coverage": [
                    "segmented Mobius through n=50000 against trial-factor brute force",
                    "segmented Liouville through n=50000 against trial-factor brute force",
                    "five seeded squarefree sign streams through n=50000 against brute force",
                    "exact integer-step W against independent prefix accumulation",
                    "J4 analytic cross and P-squared integrals against 20000-panel Simpson quadrature",
                    "registered log grid and midpoint sample counts",
                ],
            }

            if args.self_test_only:
                metadata["status"] = "SELF_TEST_PASS"
                return 0

            production_command = [str(binary), "run", str(output_dir)]
            metadata["commands"].append(production_command)
            metadata["production_started_utc"] = utc_now()
            code, seconds = tee_command(
                production_command, repo, log,
                "PHASE production start limits=S0,S4x5,S5:100000000",
            )
            metadata["elapsed_seconds"]["production"] = seconds
            metadata["production_completed_utc"] = utc_now()
            if code != 0:
                raise RuntimeError(f"production run failed with exit {code}")
            if not checks_path.exists():
                raise RuntimeError("C++ run did not write true_systems_checks.json")
            checks = json.loads(checks_path.read_text(encoding="utf-8"))
            metadata["judges"] = {
                "J1": checks["J1"]["status"],
                "J2": checks["J2"]["status"],
                "J4": checks["J4"]["status"],
            }
            metadata["checks_file"] = str(checks_path)
            metadata["postflight"]["checks_file_valid_json"] = True

            postflight: dict[str, object] = {}
            for name in STREAMS:
                grid_path = output_dir / f"{name}.csv"
                sample_path = output_dir / f"{name}_samples.csv"
                decade_path = output_dir / f"{name}_decades.csv"
                grid_header, grid_count = csv_rows(grid_path)
                sample_header, sample_count = csv_rows(sample_path)
                decade_header, decade_count = csv_rows(decade_path)
                expected = {
                    "grid_header": grid_header == ["X", "M", "W"],
                    "grid_rows": grid_count == EXPECTED_GRID_ROWS,
                    "sample_header": sample_header == ["x", "ratio"],
                    "sample_rows": sample_count == EXPECTED_SAMPLE_ROWS,
                    "decade_rows": decade_count == EXPECTED_DECADE_ROWS,
                    "decade_metrics": "ratio_variance" in decade_header and "sign_changes" in decade_header,
                }
                postflight[name] = {
                    "grid_rows": grid_count,
                    "sample_rows": sample_count,
                    "decade_rows": decade_count,
                    "checks": expected,
                }
                if not all(expected.values()):
                    raise RuntimeError(f"postflight CSV validation failed for {name}: {expected}")

            planted_header, planted_rows = csv_rows(output_dir / "S0_planted.csv")
            postflight["S0_planted"] = {
                "header": planted_header,
                "rows": planted_rows,
                "checks": {
                    "header": planted_header == ["X", "M", "W"],
                    "rows": planted_rows == 601,
                },
            }
            if planted_header != ["X", "M", "W"] or planted_rows != 601:
                raise RuntimeError("postflight J4 planted CSV validation failed")
            metadata["postflight"]["csv"] = postflight
            if any(value != "PASS" for value in metadata["judges"].values()):
                raise RuntimeError(f"one or more judges did not pass: {metadata['judges']}")
            metadata["status"] = "PASS"
        except Exception as exc:  # preserve a structured failure record
            failure = f"{type(exc).__name__}: {exc}"
            metadata["status"] = "FAIL"
            metadata["error"] = failure
            print(f"RUNNER_ERROR {failure}", flush=True)
            log.write(f"RUNNER_ERROR {failure}\n")
        finally:
            if "binary" in locals():
                try:
                    binary.unlink(missing_ok=True)
                except OSError as cleanup_error:
                    metadata["temporary_binary_cleanup"] = str(cleanup_error)
            metadata["completed_utc"] = utc_now()
            # Record actual wall time independently of child process timings.
            metadata["elapsed_seconds"]["wall_clock"] = (
                dt.datetime.fromisoformat(metadata["completed_utc"])
                - dt.datetime.fromisoformat(metadata["started_utc"])
            ).total_seconds()
            write_json(run_json_path, metadata)
            log.write(f"RUN_JSON {run_json_path}\n")
            log.flush()

    if failure is not None:
        return 1
    print(f"RUN_COMPLETE status={metadata['status']} json={run_json_path}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
