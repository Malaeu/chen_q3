#!/usr/bin/env python3
"""Run the registered integer systems after all pre-production judges pass.

Example with the repository's existing python-flint environment:
    uv run --python /path/to/rh_lean_01_2026/.venv/bin/python \
        scripts/run_integer.py --full

No dependencies are installed by this wrapper. It compiles a temporary C++
binary and writes only the integer-owned result files in this task directory.
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import tempfile
import time


PRE_RUN_COMMIT = "497a9105ae3cfe240dfe0bdf50404c4346cd4ab0"
PRE_REG_RELATIVE = "docs/routeB_bus/diag/ZERO_SENSITIVE_FAKES_2026-11-06/PREREGISTRATION.json"
OLD_RUNNER_RELATIVE = "docs/routeB_bus/diag/PRIME_PROPERTY_ABLATION_2026-11-06/scripts/run_true.py"
OLD_S0_RELATIVE = "docs/routeB_bus/diag/PRIME_PROPERTY_ABLATION_2026-11-06/S0.csv"
SYSTEMS = ("T0", "T1", "T2", "F1")


def now_utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def csv_schema(path: Path) -> tuple[list[str], int]:
    with path.open("r", encoding="utf-8", newline="") as stream:
        reader = csv.reader(stream)
        header = next(reader)
        count = sum(1 for _ in reader)
    return header, count


def tee(command: list[str], cwd: Path, log, label: str) -> tuple[int, float]:
    line = f"PHASE {label} command={json.dumps(command)}"
    print(line, flush=True)
    log.write(line + "\n")
    log.flush()
    started = time.monotonic()
    process = subprocess.Popen(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    assert process.stdout is not None
    for output in process.stdout:
        print(output, end="", flush=True)
        log.write(output)
        log.flush()
    code = process.wait()
    elapsed = time.monotonic() - started
    line = f"COMMAND_DONE phase={label} exit={code} elapsed_s={elapsed:.3f}"
    print(line, flush=True)
    log.write(line + "\n")
    log.flush()
    return code, elapsed


def verify_prereg(repo: Path, result_dir: Path) -> tuple[str, str]:
    prereg_path = result_dir / "PREREGISTRATION.json"
    prereg_bytes = prereg_path.read_bytes()
    committed = subprocess.check_output(
        ["git", "show", f"{PRE_RUN_COMMIT}:{PRE_REG_RELATIVE}"], cwd=repo
    )
    if prereg_bytes != committed:
        raise RuntimeError("local preregistration bytes differ from the pinned pre-run commit")
    prereg = json.loads(prereg_bytes.decode("utf-8"))
    if prereg.get("status") != "PRE_RUN":
        raise RuntimeError("preregistration is not PRE_RUN")
    current_head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", PRE_RUN_COMMIT, current_head], cwd=repo)
    if ancestor.returncode != 0:
        raise RuntimeError(f"pinned preregistration commit is not an ancestor of HEAD: {current_head}")
    blob = subprocess.check_output(
        ["git", "rev-parse", f"{PRE_RUN_COMMIT}:{PRE_REG_RELATIVE}"], cwd=repo, text=True
    ).strip()
    return sha256_bytes(prereg_bytes), blob


def postflight(result_dir: Path) -> dict:
    expected = {
        "T0.csv": ("T0", ["X", "M", "W"], 701),
        "T1.csv": ("T1", ["X", "M", "W"], 701),
        "T2.csv": ("T2", ["X", "M", "W"], 601),
        "F1.csv": ("F1", ["X", "M", "W"], 601),
    }
    checked: dict[str, object] = {}
    for filename, (name, header_expected, rows_expected) in expected.items():
        header, count = csv_schema(result_dir / filename)
        if header != header_expected or count != rows_expected:
            raise RuntimeError(f"invalid {filename} schema/count: {header} / {count}")
        probe_header, probe_count = csv_schema(result_dir / f"{name}_probes.csv")
        if probe_header != [
            "X", "unit_shift_sum_over_X", "adjacent_support_fraction",
            "adjacent_support_count", "adjacent_pair_count",
        ] or probe_count != rows_expected:
            raise RuntimeError(f"invalid {name} P3 probe schema/count")
        sample_header, sample_count = csv_schema(result_dir / f"{name}_samples.csv")
        sample_limit = 8000 if name in ("T0", "T1") else 7000
        if sample_header != ["x", "M", "M_over_sqrt_x", "M_over_x"] or sample_count != sample_limit:
            raise RuntimeError(f"invalid {name} sample schema/count")
        checked[name] = {
            "grid_rows": count,
            "probe_rows": probe_count,
            "sample_rows": sample_count,
            "grid_sha256": sha256_file(result_dir / filename),
            "probe_sha256": sha256_file(result_dir / f"{name}_probes.csv"),
            "sample_sha256": sha256_file(result_dir / f"{name}_samples.csv"),
        }
    p2_header, p2_count = csv_schema(result_dir / "T0_prime_p2.csv")
    if p2_header != [
        "X", "modulus", "residue", "count", "total_count", "expected_uniform",
        "normalized_imbalance", "probe_scalar",
    ] or p2_count != 701 * sum((3, 4, 5, 6)):
        raise RuntimeError("invalid T0 prime-residue P2 reference schema/count")
    p5_header, p5_count = csv_schema(result_dir / "F1_p5_probes.csv")
    if p5_header != [
        "X", "mean_absolute_defect", "defect_pair_count", "total_ordered_coprime_pairs",
        "relative_defect_pair_density",
    ] or p5_count != 601:
        raise RuntimeError("invalid F1 P5 schema/count")
    pair_header, pair_count = csv_schema(result_dir / "F1_p5_residue_pair_counts.csv")
    if pair_header != ["residue_m", "residue_n", "ordered_coprime_pair_count"] or pair_count != 4:
        raise RuntimeError("invalid F1 P5 exact residue pair count schema")
    checked["T0_prime_p2"] = {"rows": p2_count, "sha256": sha256_file(result_dir / "T0_prime_p2.csv")}
    checked["F1_p5"] = {
        "rows": p5_count,
        "sha256": sha256_file(result_dir / "F1_p5_probes.csv"),
        "residue_pair_rows": pair_count,
        "residue_pair_sha256": sha256_file(result_dir / "F1_p5_residue_pair_counts.csv"),
    }
    return checked


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-directory", type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--full", action="store_true", help="run pre-production judges then full limits")
    mode.add_argument("--judges-only", action="store_true", help="run all judges, but no production systems")
    args = parser.parse_args()

    script = Path(__file__).resolve()
    result_dir = (args.output_directory or script.parent.parent).resolve()
    repo = script.parents[5]
    judges_dir = result_dir / "integerjudges"
    judges_dir.mkdir(parents=True, exist_ok=True)
    log_path = result_dir / "integer_run.log"
    run_path = result_dir / "integer_run.json"
    run_started = time.monotonic()
    source_cpp = script.with_name("integer_systems.cpp")
    tau_script = script.with_name("integer_tau.py")
    judge_script = script.with_name("integer_judges.py")
    metadata: dict[str, object] = {
        "status": "RUNNING",
        "classification": "FINITE_DIAGNOSTIC_NOT_RH",
        "started_utc": now_utc(),
        "repo": str(repo),
        "head": None,
        "pre_run_commit": PRE_RUN_COMMIT,
        "preregistration_sha256": None,
        "preregistration_blob": None,
        "source_sha256": {
            "integer_systems.cpp": sha256_file(source_cpp),
            "run_integer.py": sha256_file(script),
            "integer_tau.py": sha256_file(tau_script),
            "integer_judges.py": sha256_file(judge_script),
        },
        "output_directory": str(result_dir),
        "limits": {"T0": 100_000_000, "T1": 100_000_000, "T2": 10_000_000, "F1": 10_000_000},
        "normalization": {
            "T0": "mu(n)",
            "T1": "mu(n)*chi4(n)",
            "T2": "Dirichlet inverse of tau(n)/n^(11/2); b(p)=-tau(p)/p^(11/2), b(p^2)=1, b(p^e)=0 for e>=3",
            "F1": "Dirichlet inverse of periodic Davenport-Heilbronn coefficients modulo 5",
            "W": "raw M_b; exact integer-step integral with Kahan accumulation; no fitted bias subtraction",
            "samples": "M/sqrt(x) and M/x are both retained",
            "T2_zero_support": "computed long-double Euler product is nonzero; no additive cancellation, prime factors originate as binary64 normalized tau values",
            "F1_zero_support": "abs(b(n))>64*long_double_epsilon*sum_abs_recurrence_terms; zero term scale yields exact-zero cutoff",
        },
        "resource_plan": {
            "T0_T1": "segmented Mobius and prime flags, approximately 6 MiB working arrays at 1 Mi-element blocks",
            "T2": "SPF uint32 table about 40 MiB plus binary64 prime weights about 80 MiB",
            "F1": "SPF about 40 MiB plus long-double coefficient array (80-160 MiB by ABI)",
            "P5": "Mertens residue and total prefixes about 80 MiB packed; temporary pre-pack copies can raise this near 160 MiB",
            "measure": "ru_maxrss is recorded as returned by the host runtime; units remain platform-defined",
        },
        "commands": [],
        "elapsed_seconds": {},
        "judges": {},
        "postflight": {},
        "truncations": [],
    }
    failure: str | None = None
    binary: Path | None = None
    temporary_root: Path | None = None
    try:
        result_dir.mkdir(parents=True, exist_ok=True)
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        metadata["head"] = head
        prereg_sha, prereg_blob = verify_prereg(repo, result_dir)
        metadata["preregistration_sha256"] = prereg_sha
        metadata["preregistration_blob"] = prereg_blob

        compiler = shutil.which("g++")
        if compiler is None:
            raise RuntimeError("g++ was not found")
        compiler_version = subprocess.check_output([compiler, "--version"], text=True).splitlines()[0]
        metadata["compiler"] = compiler
        metadata["compiler_version"] = compiler_version
        binary = Path(tempfile.gettempdir()) / f"q3_integer_systems_{os.getpid()}"
        compile_command = [compiler, "-O3", "-std=c++17", "-Wall", "-Wextra", "-pedantic", str(source_cpp), "-o", str(binary)]

        with log_path.open("w", encoding="utf-8") as log:
            metadata["commands"].append(compile_command)
            code, seconds = tee(compile_command, repo, log, "compile")
            metadata["elapsed_seconds"]["compile"] = seconds
            if code != 0:
                raise RuntimeError(f"integer C++ compile failed with exit {code}")

            self_command = [str(binary), "--self-test"]
            metadata["commands"].append(self_command)
            code, seconds = tee(self_command, repo, log, "static_self_test")
            metadata["elapsed_seconds"]["static_self_test"] = seconds
            if code != 0:
                raise RuntimeError("integer C++ self-test failed")

            # T0 is intentionally the predecessor's committed output, byte for byte.
            predecessor_s0 = repo / OLD_S0_RELATIVE
            t0_csv = result_dir / "T0.csv"
            shutil.copyfile(predecessor_s0, t0_csv)

            f1_small = judges_dir / "F1_small_inverse.csv"
            f1_prefix_command = [str(binary), "f1-prefix", str(f1_small), "500"]
            metadata["commands"].append(f1_prefix_command)
            code, seconds = tee(f1_prefix_command, repo, log, "F1_small_precision_input")
            metadata["elapsed_seconds"]["F1_small_precision_input"] = seconds
            if code != 0:
                raise RuntimeError("F1 small inverse prefix generation failed")

            preproduction_command = [
                sys.executable, str(judge_script), "--phase", "preproduction",
                "--output-directory", str(result_dir), "--f1-small-csv", str(f1_small),
            ]
            metadata["commands"].append(preproduction_command)
            code, seconds = tee(preproduction_command, repo, log, "J1_and_J4_preproduction")
            metadata["elapsed_seconds"]["J1_and_J4_preproduction"] = seconds
            if code != 0:
                raise RuntimeError("J1/J4 pre-production judges failed")

            trial_csv = judges_dir / "T1_trial_prefix_50000.csv"
            trial_command = [str(binary), "trial-prefix", str(trial_csv), "50000"]
            metadata["commands"].append(trial_command)
            code, seconds = tee(trial_command, repo, log, "T1_trial_factor_input")
            metadata["elapsed_seconds"]["T1_trial_factor_input"] = seconds
            if code != 0:
                raise RuntimeError("T1 segmented prefix generation failed")
            t1_judge_command = [
                sys.executable, str(judge_script), "--phase", "j2-t1",
                "--output-directory", str(result_dir), "--t1-trial-csv", str(trial_csv),
            ]
            metadata["commands"].append(t1_judge_command)
            code, seconds = tee(t1_judge_command, repo, log, "J2_T1_independent_trial_factor")
            metadata["elapsed_seconds"]["J2_T1_independent_trial_factor"] = seconds
            if code != 0:
                raise RuntimeError("J2 T1 independent trial-factor judge failed")

            temporary_root = Path(tempfile.mkdtemp(prefix="q3_zero_integer_j2_"))
            old_runner = repo / OLD_RUNNER_RELATIVE
            old_output = temporary_root / "old_true_runner_output"
            old_command = [
                "uv", "run", "--script", str(old_runner), "--full",
                "--output-directory", str(old_output),
            ]
            metadata["commands"].append(old_command)
            code, seconds = tee(old_command, repo, log, "J2_T0_predecessor_true_runner_replay")
            metadata["elapsed_seconds"]["J2_T0_predecessor_true_runner_replay"] = seconds
            if code != 0:
                raise RuntimeError("predecessor true runner replay failed")
            old_log = old_output / "true_systems.log"
            if old_log.exists():
                shutil.copyfile(old_log, judges_dir / "J2_old_true_runner.log")
            t0_judge_command = [
                sys.executable, str(judge_script), "--phase", "j2-t0",
                "--output-directory", str(result_dir), "--t0-csv", str(t0_csv),
                "--predecessor-s0-csv", str(predecessor_s0),
                "--rerun-s0-csv", str(old_output / "S0.csv"),
                "--rerun-checks-json", str(old_output / "true_systems_checks.json"),
            ]
            metadata["commands"].append(t0_judge_command)
            code, seconds = tee(t0_judge_command, repo, log, "J2_T0_exact_printed_replay")
            metadata["elapsed_seconds"]["J2_T0_exact_printed_replay"] = seconds
            if code != 0:
                raise RuntimeError("J2 T0 exact printed-value replay failed")

            finalize_command = [sys.executable, str(judge_script), "--phase", "finalize", "--output-directory", str(result_dir)]
            metadata["commands"].append(finalize_command)
            code, seconds = tee(finalize_command, repo, log, "judge_freeze")
            metadata["elapsed_seconds"]["judge_freeze"] = seconds
            if code != 0:
                raise RuntimeError("one or more integer judges did not pass")
            frozen_judges = json.loads((judges_dir / "JUDGES.json").read_text(encoding="utf-8"))
            if frozen_judges.get("status") != "PASS":
                raise RuntimeError("pre-production judge receipt is not PASS")
            metadata["judges"] = frozen_judges
            if args.judges_only:
                metadata["status"] = "PRE_PRODUCTION_JUDGES_PASS"
                print(f"JUDGES_COMPLETE status=PASS json={run_path}", flush=True)
                return 0

            with tempfile.TemporaryDirectory(prefix="q3_zero_integer_tau_") as tau_tmp:
                tau_bin = Path(tau_tmp) / "tau_prime_weights.bin"
                tau_receipt = judges_dir / "T2_tau_generation.json"
                tau_command = [
                    sys.executable, str(tau_script), "--limit", "10000000",
                    "--output", str(tau_bin), "--receipt", str(tau_receipt),
                ]
                metadata["commands"].append(tau_command)
                code, seconds = tee(tau_command, repo, log, "T2_exact_tau_series_prime_weights")
                metadata["elapsed_seconds"]["T2_exact_tau_series_prime_weights"] = seconds
                if code != 0:
                    raise RuntimeError("exact T2 tau series generation failed")
                tau_meta = json.loads(tau_receipt.read_text(encoding="utf-8"))
                metadata["T2_tau_generation"] = tau_meta
                production_command = [str(binary), "run", str(result_dir), str(tau_bin)]
                metadata["commands"].append(production_command)
                metadata["production_started_utc"] = now_utc()
                code, seconds = tee(production_command, repo, log, "integer_systems_full_limits")
                metadata["elapsed_seconds"]["production"] = seconds
                metadata["production_completed_utc"] = now_utc()
                if code != 0:
                    raise RuntimeError(f"integer systems production failed with exit {code}")

            metadata["postflight"] = postflight(result_dir)
            metadata["status"] = "PASS"
    except Exception as exc:
        failure = f"{type(exc).__name__}: {exc}"
        metadata["status"] = "FAIL"
        metadata["error"] = failure
        print(f"RUNNER_ERROR {failure}", flush=True)
    finally:
        if binary is not None:
            try:
                binary.unlink(missing_ok=True)
            except OSError as exc:
                metadata["temporary_binary_cleanup_error"] = str(exc)
        if temporary_root is not None:
            try:
                shutil.rmtree(temporary_root)
            except OSError as exc:
                metadata["temporary_j2_cleanup_error"] = str(exc)
        metadata["completed_utc"] = now_utc()
        metadata["elapsed_seconds"]["wall_clock"] = (
            dt.datetime.fromisoformat(metadata["completed_utc"])
            - dt.datetime.fromisoformat(metadata["started_utc"])
        ).total_seconds()
        metadata["elapsed_seconds"]["monotonic_wall_clock"] = time.monotonic() - run_started
        metadata["ru_maxrss_children_platform_units"] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        write_json(run_path, metadata)
        if log_path.exists():
            with log_path.open("a", encoding="utf-8") as log:
                log.write(f"RUN_JSON {run_path}\n")

    if failure is not None:
        return 1
    print(f"RUN_COMPLETE status={metadata['status']} json={run_path}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
