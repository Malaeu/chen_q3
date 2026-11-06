#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Run the pre-registered S1-S3 fake systems and their finite enumeration judges.

Examples:
  uv run --script docs/routeB_bus/diag/PRIME_PROPERTY_ABLATION_2026-11-06/scripts/run_fake.py judge
  uv run --script docs/routeB_bus/diag/PRIME_PROPERTY_ABLATION_2026-11-06/scripts/run_fake.py run
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import shlex
import statistics
import subprocess
import sys
import tempfile
import time
from typing import Any

HERE = Path(__file__).resolve().parent
OUT = HERE.parent
CPP = HERE / "fake_systems.cpp"
PREREG = OUT / "PREREGISTRATION.json"
CHECKS = OUT / "FAKE_CHECKS.json"
LIMIT = 10_000_000
PREREG_COMMIT = '8e2e29a866600c16cf38127ff5325ac97dc2880e'


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")



def validate_prereg_pin() -> dict[str, Any]:
    root = Path(subprocess.run(
        ["git", "-C", str(OUT), "rev-parse", "--show-toplevel"],
        text=True, capture_output=True, check=True,
    ).stdout.strip())
    head = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        text=True, capture_output=True, check=True,
    ).stdout.strip()
    subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", PREREG_COMMIT, "HEAD"],
        text=True, capture_output=True, check=True,
    )
    rel = PREREG.relative_to(root).as_posix()
    pinned = subprocess.run(
        ["git", "-C", str(root), "show", f"{PREREG_COMMIT}:{rel}"],
        capture_output=True, check=True,
    ).stdout
    if pinned != PREREG.read_bytes():
        raise RuntimeError("working preregistration bytes differ from the committed pre-run pin")
    return {
        "repo_root": str(root),
        "head_at_run": head,
        "pinned_prereg_commit": PREREG_COMMIT,
        "pinned_commit_is_ancestor": True,
        "current_prereg_matches_pinned_git_show": True,
        "prereg_path": rel,
    }


def preflight_grids(limit: int) -> dict[str, Any]:
    max_decade = int(math.floor(math.log10(limit) + 1e-12))
    grid: list[float] = []
    for d in range(1, max_decade + 1):
        for i in range(100):
            x = math.pow(10.0, d + i / 100.0)
            if x < limit:
                grid.append(x)
    if not grid or grid[-1] != float(limit):
        grid.append(float(limit))
    samples_by_decade = {d: 0 for d in range(max_decade + 1)}
    samples: list[float] = []
    for d in range(max_decade + 1):
        for i in range(1000):
            x = math.pow(10.0, d + (i + 0.5) / 1000.0)
            if x < limit:
                samples_by_decade[d] += 1
                samples.append(x)
    if limit == LIMIT:
        if len(grid) != 601 or grid[-1] != float(limit):
            raise RuntimeError(f"pre-run grid must have 601 points ending at {limit}")
        if any(a >= b for a, b in zip(grid, grid[1:])):
            raise RuntimeError("pre-run X grid is not strictly increasing")
        if any(10.0**d not in grid for d in range(1, 8)):
            raise RuntimeError("pre-run X grid omitted an exact power of ten")
        active_counts = {d: samples_by_decade[d] for d in range(max_decade)}
        if len(samples) != 7000 or active_counts != {d: 1000 for d in range(7)}:
            raise RuntimeError(f"pre-run samples must be 7000 (1000 per decade), got {samples_by_decade}")
        if any(a >= b for a, b in zip(samples, samples[1:])):
            raise RuntimeError("pre-run sample grid is not strictly increasing")
    return {
        "status": "PASS",
        "grid_rows": len(grid),
        "grid_first": grid[0],
        "grid_last": grid[-1],
        "grid_strictly_increasing": all(a < b for a, b in zip(grid, grid[1:])),
        "sample_rows": len(samples),
        "samples_per_decade": {str(d): n for d, n in samples_by_decade.items()},
    }


def compile_cpp(binary: Path) -> dict[str, Any]:
    cxx = shlex.split(os.environ.get("CXX", "c++"))
    command = [*cxx, "-std=c++17", "-O3", "-DNDEBUG", str(CPP), "-o", str(binary)]
    result = subprocess.run(command, text=True, capture_output=True)
    if result.returncode:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise RuntimeError(f"C++ compile failed with exit {result.returncode}")
    version = subprocess.run([*cxx, "--version"], text=True, capture_output=True, check=True)
    return {
        "command": command,
        "compiler_version": (version.stdout or version.stderr).splitlines()[0],
        "source_sha256": sha256(CPP),
    }


def invoke(binary: Path, args: list[str], label: str = "") -> dict[str, Any]:
    proc = subprocess.Popen(
        [str(binary), *args], text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        bufsize=1,
    )
    assert proc.stdout is not None and proc.stderr is not None
    for line in proc.stderr:
        prefix = f"[{label}] " if label else ""
        sys.stderr.write(prefix + line)
        sys.stderr.flush()
    stdout = proc.stdout.read()
    status = proc.wait()
    if status:
        raise RuntimeError(f"fake_systems exited {status}: {stdout.strip()}")
    try:
        return json.loads(stdout.strip().splitlines()[-1])
    except (ValueError, IndexError) as exc:
        raise RuntimeError(f"fake_systems returned no JSON summary: {stdout!r}") from exc


def load_groups(path: Path) -> dict[float, tuple[int, int]]:
    result: dict[float, tuple[int, int]] = {}
    with path.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            result[float(row["x"])] = (int(row["N_delta"]), int(row["M_delta"]))
    return result


def brute_exponent_vectors(generators: list[float], limit: float) -> dict[float, tuple[int, int]]:
    """Independent nested-exponent enumeration, separate from the C++ tuple DFS."""
    counts: dict[float, list[int]] = {}

    def recurse(index: int, product: float, mu: int) -> None:
        if index == len(generators):
            entry = counts.setdefault(product, [0, 0])
            entry[0] += 1
            entry[1] += mu
            return
        q = generators[index]
        q_power = 1.0
        exponent = 0
        while product * q_power <= limit:
            if exponent == 0:
                next_mu = mu
            elif exponent == 1:
                next_mu = -mu if mu else 0
            else:
                next_mu = 0
            recurse(index + 1, product * q_power, next_mu)
            q_power *= q
            exponent += 1

    recurse(0, 1.0, 1)
    return {x: (n, m) for x, (n, m) in counts.items()}


def compare_enumerators(
    binary: Path, generators: list[float], limit: int, label: str, temp: Path
) -> dict[str, Any]:
    genfile = temp / f"{label}.generators.txt"
    genfile.write_text("".join(f"{q:.17g}\n" for q in generators), encoding="ascii")
    prefix = temp / label
    cxx_summary = invoke(binary, ["enumerate", str(limit), str(genfile), str(prefix)], label)
    cxx_groups = load_groups(Path(str(prefix) + ".groups.csv"))
    brute = brute_exponent_vectors(generators, limit)
    if cxx_groups != brute:
        missing = sorted(set(brute) - set(cxx_groups))[:5]
        extra = sorted(set(cxx_groups) - set(brute))[:5]
        wrong = [
            (x, cxx_groups[x], brute[x])
            for x in sorted(set(brute) & set(cxx_groups))
            if cxx_groups[x] != brute[x]
        ][:5]
        raise AssertionError(
            f"{label}: C++/independent multiplicity mismatch; "
            f"missing={missing}, extra={extra}, wrong={wrong}"
        )
    return {
        "label": label,
        "limit": limit,
        "generator_count": len(generators),
        "distinct_numeric_products": len(brute),
        "semigroup_objects_with_multiplicity": sum(n for n, _ in brute.values()),
        "cxx_summary": cxx_summary,
        "independent_nested_exponent_vectors": "PASS",
    }


def run_judges(binary: Path, temp: Path) -> dict[str, Any]:
    small_limit = 500
    generated_path = temp / "S1_seed1101_generators.txt"
    generator_summary = invoke(
        binary,
        ["generators", "S1", "1101", "0", str(small_limit), str(generated_path)],
        "judge-S1-generator",
    )
    actual_s1 = [
        float(line.strip())
        for line in generated_path.read_text(encoding="ascii").splitlines()
        if line.strip()
    ]
    actual_test = compare_enumerators(binary, actual_s1, small_limit, "actual_S1_seed1101", temp)

    collision_24 = compare_enumerators(binary, [2.0, 4.0], 64, "collision_2_4", temp)
    groups_24 = load_groups(temp / "collision_2_4.groups.csv")
    if groups_24.get(4.0) != (2, -1):
        raise AssertionError(f"[2,4] collision at product 4 should have (N,mu)=(2,-1), got {groups_24.get(4.0)}")
    collision_236 = compare_enumerators(binary, [2.0, 3.0, 6.0], 128, "collision_2_3_6", temp)
    groups_236 = load_groups(temp / "collision_2_3_6.groups.csv")
    if groups_236.get(6.0) != (2, 0):
        raise AssertionError(f"[2,3,6] collision at product 6 should have (N,mu)=(2,0), got {groups_236.get(6.0)}")

    density_at = {}
    for x in (10, 100, 500):
        n = sum(count for value, (count, _) in load_groups(
            temp / "actual_S1_seed1101.groups.csv"
        ).items() if value <= x)
        density_at[str(x)] = {"N": n, "N_over_x": n / x}
    return {
        "status": "PASS",
        "contract": "each generator-index exponent vector contributes one N object; mu is zero if any exponent >=2, otherwise (-1)^total_degree; equal numeric products aggregate",
        "actual_S1_small_case": {
            **actual_test,
            "generator_draw": generator_summary,
            "seed": 1101,
        },
        "adversarial_collisions": {
            "generators_2_4": {
                **collision_24,
                "product_4_N_mu": {"N": 2, "mu": -1},
            },
            "generators_2_3_6": {
                **collision_236,
                "product_6_N_mu": {"N": 2, "mu": 0},
            },
        },
        "finite_density_diagnostic_only": {
            "system": "actual S1 seed 1101",
            "N_over_x": density_at,
            "interpretation": "These small finite-X values check neither asymptotic convergence nor RH-quality counting.",
            "asymptotic_convergence_claimed": False,
        },
    }


def expected_runs(prereg: dict[str, Any]) -> list[dict[str, int | str]]:
    jobs: list[dict[str, int | str]] = []
    for seed in prereg["seeds"]["S1"]:
        jobs.append({"system": "S1", "seed": seed, "y": 0})
    for y in prereg["hybrid_y"]:
        for seed in prereg["seeds"]["S2"]:
            jobs.append({"system": "S2", "seed": seed, "y": y})
    for seed in prereg["seeds"]["S3"]:
        jobs.append({"system": "S3", "seed": seed, "y": 0})
    return jobs


def prefix_for(job: dict[str, int | str]) -> Path:
    system = str(job["system"])
    seed = int(job["seed"])
    if system == "S2":
        return OUT / f"S2_y{int(job['y'])}_seed{seed}"
    return OUT / f"{system}_seed{seed}"


def validate_csv_outputs(prefix: Path, summary: dict[str, Any], limit: int) -> dict[str, Any]:
    with prefix.with_suffix(".csv").open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        rows = list(reader)
    xs = [float(row["X"]) for row in rows]
    if len(xs) != 601 or any(a >= b for a, b in zip(xs, xs[1:])) or xs[-1] != limit:
        raise AssertionError(f"{prefix.name}: grid must have 601 strictly increasing rows ending at {limit}")
    if xs[0] != 10.0 or any(10.0**d not in xs for d in range(1, 8)):
        raise AssertionError(f"{prefix.name}: grid must start at 10 and contain exact powers 10..1e7")
    if int(rows[-1]["N"]) != int(summary["semigroup_objects"]):
        raise AssertionError(f"{prefix.name}: N(limit) disagrees with enumerated multiplicity total")

    sample_path = Path(str(prefix) + "_samples.csv")
    with sample_path.open(newline="", encoding="utf-8") as stream:
        sample_rows = list(csv.DictReader(stream))
    decade_counts = {str(d): 0 for d in range(7)}
    sample_xs: list[float] = []
    for row in sample_rows:
        d = row["decade"]
        decade_counts[d] += 1
        x = float(row["x"])
        sample_xs.append(x)
        if not (10.0**int(d) <= x < 10.0 ** (int(d) + 1) and x < limit):
            raise AssertionError(f"{prefix.name}: sample {x} is outside its half-open decade")
        if abs(float(row["ratio"]) - int(row["M"]) / math.sqrt(x)) > 1e-14:
            raise AssertionError(f"{prefix.name}: sample ratio mismatch at x={x}")
    if len(sample_rows) != 7000 or set(decade_counts.values()) != {1000}:
        raise AssertionError(f"{prefix.name}: expected exactly 7000 samples (1000 per decade), got {decade_counts}")
    if any(a >= b for a, b in zip(sample_xs, sample_xs[1:])):
        raise AssertionError(f"{prefix.name}: samples are not strictly increasing")

    decade_path = Path(str(prefix) + "_decades.csv")
    with decade_path.open(newline="", encoding="utf-8") as stream:
        decade_rows = list(csv.DictReader(stream))
    if len(decade_rows) != 7 or [int(row["sample_count"]) for row in decade_rows] != [1000] * 7:
        raise AssertionError(f"{prefix.name}: expected seven sample decades")
    return {
        "grid_rows": len(rows),
        "grid_strictly_increasing": True,
        "grid_max_is_limit": True,
        "sample_rows": len(sample_rows),
        "samples_per_decade": decade_counts,
        "decade_rows": len(decade_rows),
        "N_limit_matches_semigroup_objects": True,
    }


def run_job(binary: Path, job: dict[str, int | str], limit: int, label: str) -> tuple[dict[str, Any], dict[str, Any]]:
    prefix = prefix_for(job)
    args = [
        "run", str(job["system"]), str(job["seed"]), str(job["y"]),
        str(limit), str(prefix),
    ]
    started = time.monotonic()
    summary = invoke(binary, args, label)
    elapsed = time.monotonic() - started
    validation = validate_csv_outputs(prefix, summary, limit)
    summary["observed_wall_seconds_including_python_validation"] = elapsed
    summary["files"] = [
        prefix.name + ".csv",
        prefix.name + "_samples.csv",
        prefix.name + "_decades.csv",
    ]
    summary["output_validation"] = validation
    return summary, validation


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("judge", "run", "all"))
    parser.add_argument("--limit", type=int, default=LIMIT)
    args = parser.parse_args()
    if args.limit != LIMIT:
        parser.error(f"production runs are pinned to X_max={LIMIT}; small judges use their own limits")
    prereg_pin = validate_prereg_pin()
    grid_preflight = preflight_grids(args.limit)
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    if prereg.get("status") != "PRE_RUN":
        raise RuntimeError("preregistration is not PRE_RUN")
    if prereg.get("limits", {}).get("S1") != LIMIT or prereg.get("limits", {}).get("S2") != LIMIT or prereg.get("limits", {}).get("S3") != LIMIT:
        raise RuntimeError("preregistered fake-system limits do not match runner")
    prereg_sha = sha256(PREREG)
    jobs = expected_runs(prereg)
    expected_count = len(jobs)
    if expected_count != 17:
        raise RuntimeError(f"expected 17 preregistered fake runs, found {expected_count}")

    with tempfile.TemporaryDirectory(prefix="q3-ablation-fake-") as td:
        temp = Path(td)
        binary = temp / "fake_systems"
        toolchain = compile_cpp(binary)
        checks = {
            "schema": "prime_property_fake_checks.v1",
            "task_commit": prereg["task_commit"],
            "preregistration_sha256": prereg_sha,
            "preregistration_pin_validation": prereg_pin,
            "pre_run_grid_validation": grid_preflight,
            "code_sha256": {
                "fake_systems.cpp": sha256(CPP),
                "run_fake.py": sha256(Path(__file__).resolve()),
            },
            "toolchain": toolchain,
            "small_case_judges": run_judges(binary, temp),
            "production_limit": LIMIT,
            "rho_hat_note": "rho_hat=N(1e7)/1e7 is a finite-range fit used only for count_error; it is not an asymptotic density or RH-quality claim.",
            "production_runs": [],
            "status": "JUDGES_PASS",
            "updated_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        }
        write_json(CHECKS, checks)
        print(
            "JUDGES PASS: S1 seed 1101 exponent-vector brute force, two adversarial "
            "collision cases, finite density diagnostic only.",
            flush=True,
        )
        if args.action == "judge":
            print(f"checks: {CHECKS}")
            return 0

        completed: set[tuple[str, int, int]] = set()
        timings: list[float] = []
        completed = {(r["system"], int(r["seed"]), int(r["y"])) for r in checks["production_runs"]}
        todo = [job for job in jobs if (str(job["system"]), int(job["seed"]), int(job["y"])) not in completed]
        timings = [
            float(row["observed_wall_seconds_including_python_validation"])
            for row in checks["production_runs"]
        ]
        total = len(jobs)
        for job in todo:
            index = len(completed) + 1
            mean_time = statistics.mean(timings) if timings else None
            eta = "unknown (first full run establishes baseline)"
            if mean_time is not None:
                eta = f"~{mean_time * (total - len(completed) - 1):.0f}s remaining"
            label = f"{index:02d}/{total:02d} {job['system']} seed={job['seed']} y={job['y']} ETA_total={eta}"
            print(f"[{index:02d}/{total:02d}] START {job['system']} seed={job['seed']} y={job['y']} ETA_total={eta}", flush=True)
            summary, _ = run_job(binary, job, LIMIT, label)
            checks["production_runs"].append(summary)
            completed.add((str(job["system"]), int(job["seed"]), int(job["y"])))
            timings.append(float(summary["observed_wall_seconds_including_python_validation"]))
            checks["status"] = "RUNNING"
            checks["updated_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
            write_json(CHECKS, checks)
            print(
                f"[{index:02d}/{total:02d}] DONE elapsed="
                f"{summary['observed_wall_seconds_including_python_validation']:.1f}s "
                f"objects={summary['semigroup_objects']} rho_hat={summary['rho_hat_finite_only']:.9g}",
                flush=True,
            )

        checks["production_runs"].sort(
            key=lambda r: (r["system"], int(r["y"]), int(r["seed"]))
        )
        checks["status"] = "ALL_17_RUNS_PASS"
        checks["updated_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        checks["density_scope"] = (
            "power_density and adjacent_density_drift are finite-range observations; "
            "rho_hat remains a fit over [1, 1e7], not a proved limit."
        )
        write_json(CHECKS, checks)
        print(f"ALL 17 FAKE RUNS PASS; checks: {CHECKS}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
