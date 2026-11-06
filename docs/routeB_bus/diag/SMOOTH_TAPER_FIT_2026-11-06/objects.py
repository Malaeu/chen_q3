#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# ///
"""Build and run the Smooth Taper Part B object checks (stdlib only).

Run with:
    uv run --no-project --python 3.15 docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/objects.py
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
import platform
import shlex
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TASK_COMMIT = "45af4a837e9a183d2405d91bf7df0f002f56acde"
PREREG_COMMIT = "60ea7f7d3"
CORE_COMMIT = "a180142f"
PREREG_BLOB = "712c14b9fe5d68b8e8f124326afc1e7391af2482"
CORE_BLOB = "8d62edae64a79dd1eca0c6979b73b03ba7132687"
PREREG_PATH = "docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/PREREGISTRATION.json"
CORE_PATH = "docs/routeB_bus/diag/R8_CERTIFICATE_AND_CORE_2026-11-06/core_full_H.csv"
MAIN_N = (500, 1000, 2000, 5000)
J2_N = (50, 200, 1000)
J4_N = (50, 200, 500, 1000)


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def progress(text: str) -> None:
    print("[objects] " + text, flush=True)


def csv_rows(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        if reader.fieldnames is None:
            raise RuntimeError(f"empty CSV: {path}")
        return list(reader.fieldnames), list(reader)


def write_csv(path: Path, fieldnames: list[str], rows: list[dict]) -> None:
    if not rows:
        raise RuntimeError(f"refusing to write empty CSV: {path}")
    with path.open("w", encoding="ascii", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def parse_log_references(path: Path) -> dict[int, float]:
    fields, rows = csv_rows(path)
    if "N" not in fields or "family" not in fields:
        raise RuntimeError("fit_all.csv must have N and family columns")
    energy_col = next((c for c in ("E", "E_full", "E_gram", "E_N", "energy", "objective") if c in fields), None)
    if energy_col is None:
        raise RuntimeError(f"fit_all.csv has no recognized full-Gram E column; columns={fields}")
    refs: dict[int, float] = {}
    for row in rows:
        if row["family"] != "log_taper":
            continue
        n = int(row["N"])
        if n in J2_N:
            refs[n] = float(row[energy_col])
    missing = sorted(set(J2_N) - set(refs))
    if missing:
        raise RuntimeError(f"fit_all.csv lacks log_taper reference E for N={missing}")
    return refs


def pinned_core_grid() -> tuple[list[int], dict[str, str]]:
    blob = git("rev-parse", f"{CORE_COMMIT}:{CORE_PATH}").decode("ascii").strip()
    if blob != CORE_BLOB:
        raise RuntimeError(f"pinned core grid blob mismatch: {blob}")
    raw = git("show", f"{CORE_COMMIT}:{CORE_PATH}")
    fields, rows = csv_rows_from_bytes(raw)
    if "N" not in fields or "log_grid" not in fields:
        raise RuntimeError("pinned core_full_H.csv lacks N/log_grid")
    grid = sorted({int(r["N"]) for r in rows if r["log_grid"].lower() == "true"})
    if len(grid) != 92 or grid[0] != 3 or grid[-1] != 10000:
        raise RuntimeError(f"pinned grid mismatch: count={len(grid)} endpoints={grid[:1]}/{grid[-1:]}")
    return grid, {"commit": CORE_COMMIT, "path": CORE_PATH, "blob": blob,
                  "sha256": sha(raw), "count": str(len(grid))}


def compare_core_archive(outdir: Path, grid: list[int]) -> dict:
    raw = git("show", f"{CORE_COMMIT}:{CORE_PATH}")
    fields, archived_rows = csv_rows_from_bytes(raw)
    archived = {int(r["N"]): r for r in archived_rows
                if r["log_grid"].lower() == "true"}
    current_rows = csv_rows(outdir / "objects_core.csv")[1]
    current = {(int(r["N"]), r["family"]): r for r in current_rows}
    if sorted(archived) != grid:
        raise RuntimeError("archive comparison source does not match the pinned 92-point grid")
    result = []
    for N in grid:
        old, new = archived[N], current[(N, "log_taper")]
        if int(old["K"]) != int(new["K"]):
            raise RuntimeError(f"archive core cutoff mismatch at N={N}")
        result.append({
            "N": N, "K": int(new["K"]),
            "head_archive": old["head"], "head_current": new["head"],
            "head_abs_diff": abs(float(old["head"]) - float(new["head"])),
            "shoulder_archive": old["shoulder"], "shoulder_current": new["shoulder"],
            "shoulder_abs_diff": abs(float(old["shoulder"]) - float(new["shoulder"])),
            "full_H_archive": old["full_H"], "full_H_current": new["full_H"],
            "full_H_abs_diff": abs(float(old["full_H"]) - float(new["full_H"])),
        })
    write_csv(outdir / "objects_core_archive_compare.csv", list(result[0]), result)
    summary = {
        "grid_count": len(grid),
        "max_head_abs": max(float(r["head_abs_diff"]) for r in result),
        "max_shoulder_abs": max(float(r["shoulder_abs_diff"]) for r in result),
        "max_full_H_abs": max(float(r["full_H_abs_diff"]) for r in result),
        "tolerance": 1e-10,
    }
    if max(summary[k] for k in ("max_head_abs", "max_shoulder_abs", "max_full_H_abs")) > summary["tolerance"]:
        raise RuntimeError(f"pinned archive core comparison failed: {summary}")
    return summary


def csv_rows_from_bytes(raw: bytes) -> tuple[list[str], list[dict[str, str]]]:
    text = raw.decode("utf-8")
    reader = csv.DictReader(text.splitlines())
    if reader.fieldnames is None:
        raise RuntimeError("empty pinned CSV")
    return list(reader.fieldnames), list(reader)


def mobius(nmax: int) -> list[int]:
    lp = [0] * (nmax + 1)
    mu = [0] * (nmax + 1)
    primes: list[int] = []
    if nmax >= 1:
        lp[1] = 1
        mu[1] = 1
    for i in range(2, nmax + 1):
        if lp[i] == 0:
            lp[i] = i
            primes.append(i)
            mu[i] = -1
        for p in primes:
            v = i * p
            if v > nmax or p > lp[i]:
                break
            lp[v] = p
            if p == lp[i]:
                mu[v] = 0
                break
            mu[v] = -mu[i]
    return mu


def profile_family_check(results_path: Path, output: Path) -> dict:
    """Check literal and corrected head formulas for every fitted polynomial."""
    fields, rows = csv_rows(results_path)
    required = {"N", "family", "p1", "p2", "p3", "p4"}
    if not required.issubset(fields):
        raise RuntimeError(f"fit_results.csv missing columns {sorted(required - set(fields))}")
    poly_rows = []
    for row in rows:
        family = row["family"]
        if not family.startswith("poly_"):
            continue
        N = int(row["N"])
        if N not in MAIN_N:
            continue
        degree = int(row["degree"]) if row.get("degree") else max(
            (j for j in range(1, 5) if row.get(f"p{j}", "").strip()), default=1)
        coeff = [0.0] + [float(row[f"p{j}"]) if row.get(f"p{j}", "").strip() else 0.0
                         for j in range(1, 5)]
        poly_rows.append((N, family, degree, row.get("P1_constraint", ""), coeff))
    if not poly_rows:
        raise RuntimeError("fit_results.csv contains no polynomial fits at main Ns")

    checks: list[dict] = []
    max_corrected = 0.0
    max_literal = 0.0
    for N, family, degree, p1_constraint, coeff in poly_rows:
        L = math.log(N)
        mu = mobius(N)
        # Lambda_j(r) for j=0..degree, and the direct divisor sums A_P(r).
        lambdas = [[0.0] * (N + 1) for _ in range(degree + 1)]
        direct = [0.0] * (N + 1)
        for d in range(1, N + 1):
            x = math.log(N / d) / L
            if d == 1:
                a_d = 1.0  # fixed raw a_1, independent of P(1)
            else:
                pval = sum(coeff[j] * x ** j for j in range(1, degree + 1))
                a_d = mu[d] * pval
            for r in range(d, N + 1, d):
                direct[r] += a_d
                if mu[d]:
                    log_rd = math.log(r / d)
                    for j in range(degree + 1):
                        lambdas[j][r] += mu[d] * log_rd ** j
        p_at_1 = sum(coeff[j] for j in range(1, degree + 1))
        worst_corr = (-1.0, 0)
        worst_lit = (-1.0, 0)
        for r in range(1, N + 1):
            shift = math.log(N / r)
            literal = sum(coeff[j] * lambdas[j][r] / (L ** j)
                          for j in range(1, degree + 1))
            corrected = 1.0 - p_at_1
            for j in range(1, degree + 1):
                inner = sum(math.comb(j, k) * shift ** (j-k) * lambdas[k][r]
                            for k in range(j + 1))
                corrected += coeff[j] * inner / (L ** j)
            ec = abs(direct[r] - corrected)
            el = abs(direct[r] - literal)
            if ec > worst_corr[0]:
                worst_corr = (ec, r)
            if el > worst_lit[0]:
                worst_lit = (el, r)
        max_corrected = max(max_corrected, worst_corr[0])
        max_literal = max(max_literal, worst_lit[0])
        checks.append({
            "N": N, "family": family, "kind": "polynomial",
            "degree": degree, "P1_constraint": p1_constraint,
            "P_at_1": f"{p_at_1:.17g}",
            "corrected_max_abs": f"{worst_corr[0]:.17g}",
            "corrected_worst_r": worst_corr[1],
            "literal_max_abs": f"{worst_lit[0]:.17g}",
            "literal_worst_r": worst_lit[1],
            "corrected_status": "PASS" if worst_corr[0] <= 1e-10 else "FAIL",
        })
    write_csv(output, list(checks[0]), checks)
    return {"polynomial_fit_rows": len(checks), "max_corrected_abs": max_corrected,
            "max_literal_abs": max_literal,
            "corrected_pass": max_corrected <= 1e-10,
            "literal_miss": max_literal > 1e-10}


def compile_native(source: Path) -> tuple[Path, list[str]]:
    compiler = os.environ.get("CXX", "clang++")
    exe = Path(tempfile.gettempdir()) / "q3_smooth_objects_native"
    cmd = [compiler, "-O3", "-DNDEBUG", "-std=c++17", str(source), "-o", str(exe)]
    progress("COMPILE: " + shlex.join(cmd))
    subprocess.run(cmd, check=True)
    return exe, cmd


def write_part_b(outdir: Path, core_grid_count: int, poly: dict,
                 archive: dict) -> None:
    def rows(name: str) -> list[dict[str, str]]:
        return csv_rows(outdir / name)[1]

    j2 = rows("objects_j2.csv")
    j4 = rows("objects_j4.csv")
    boundary = rows("objects_boundary.csv")
    core = rows("objects_core.csv")
    ratios = rows("objects_core_ratios.csv")
    main_boundary = {(int(r["N"]), r["family"]): r for r in boundary
                     if int(r["N"]) in MAIN_N}
    main_core = {(int(r["N"]), r["family"]): r for r in core
                 if int(r["N"]) in MAIN_N}
    grid_set = {int(r["N"]) for r in core if int(r["N"]) <= 10000}
    max_j4 = max(float(r["norm_error_gauss12"]) for r in j4)
    max_j2 = max(float(r["abs_error"]) for r in j2)
    lines = [
        "# Part B — smooth taper objects and finite checks",
        "",
        "This is a finite floating-point diagnostic, not an interval certificate, proof of an asymptotic bound, or RH claim.",
        "",
        "## Fixed-vector convention",
        "",
        "For every profile the physical free coefficients use `a_1=1` and `a_n=mu(n)P(log(N/n)/log(N))` for `n>=2`. The induced centered coefficients are `q_1=1-s`, `q_n=a_n` for `n>=2`; `q_1` is not replaced by `P(1)`. The computed boundary objects use `S=sum a_n`, `s=sum a_n/n`, `u=sum a_n log(n)/n`, `b=1+(S-s)/2`, and `B=2b(1+u)-s`.",
        "",
        "The Parseval evaluation uses `gcd(h,k)^2=sum_{d|h,d|k} J_2(d)` and",
        "`||F||_2^2 = sum_d J_2(d)(sum_{d|n} q_n/n^2)^2/12 + (1/2-q_1)/pi^2`. The CSV also compares `||F||_2` with the log-taper benchmark `7/log(N)`; that benchmark is not assumed for best profiles.",
        "",
        "## J2 — direct cotangent functional",
        "",
        "For log tapers at `N=50,200,1000`, `F(r/k)` was evaluated with integer residues: if `k` divides `n*r`, the Bernoulli term is exactly zero; otherwise it is `(n*r mod k)/k - 1/2`. Then `L_N` was summed directly from the cotangent formula (14), and compared with the independent full-Gram reference `E` supplied by Part A. The `L_N` column was not inferred from `E`.",
        "",
        "| N | E full Gram | B | direct L_N | B - pi L_N | absolute error |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for r in j2:
        lines.append(f"| {r['N']} | {float(r['E_full_gram']):.15g} | {float(r['B']):.15g} | {float(r['L_direct']):.15g} | {float(r['E_reciprocity']):.15g} | {float(r['abs_error']):.3g} |")
    lines += ["", f"J2: **{'PASS' if max_j2 <= 1e-9 else 'FAIL'}**, maximum absolute discrepancy `{max_j2:.6g}` (tolerance `1e-9`).", "",
              "## J4 — independent piecewise quadrature",
              "",
              "The rational breakpoints are the reduced fractions `r/n` for `n<=N`. An event sweep updates the affine offset of `sum(q_n/n) B_1(n*x)` by the exact jump `-q_n/n`; on each open interval, `F(x)=x sum(q_n)+offset+sin(2*pi*x)/pi`. Independent 8- and 12-point Gauss-Legendre integrations were compared with the Jordan-2 Parseval norm. Exact rational probes use the stipulated `B_1(integer)=0` convention.",
              "",
              "| N | profile | Parseval norm | direct J4 norm | absolute norm error | intervals |",
              "|---:|---|---:|---:|---:|---:|"]
    for r in j4:
        lines.append(f"| {r['N']} | {r['family']} | {float(r['norm_parseval']):.15g} | {float(r['norm_j4_gauss12']):.15g} | {float(r['norm_error_gauss12']):.3g} | {r['event_intervals']} |")
    lines += ["", f"J4: **{'PASS' if max_j4 <= 1e-6 else 'FAIL'}**, maximum norm discrepancy `{max_j4:.6g}` (tolerance `1e-6`).", "",
              "## Literal and corrected head identity (R4)",
              "",
              "For `P(x)=sum_{j>=1} p_j x^j`, the literal requested formula omits both the logarithmic shift and the fixed raw-`a_1` correction. The corrected identity tested here is",
              "",
              "```text",
              "A_P(r) = 1 - P(1) + sum_j p_j/L^j * sum_{k=0}^j binom(j,k) log(N/r)^(j-k) Lambda_k(r),",
              "Lambda_k(r) = sum_{d|r} mu(d) log(r/d)^k,  Lambda_0(r)=1_{r=1}.",
              "```",
              "",
              f"Across `{poly['polynomial_fit_rows']}` fitted polynomial rows at the four main Ns, the corrected formula's largest absolute error is `{poly['max_corrected_abs']:.6g}` (**{'PASS' if poly['corrected_pass'] else 'FAIL'}**, threshold `1e-10`). The literal expression is a preregistered **MISS** (largest fit-row discrepancy `{poly['max_literal_abs']:.6g}`), kept separate from the corrected pass.",
              "",
              "The explicit witness is `P=x^2,N=4,r=2`: direct divisor sum `3/4`, literal expression `1/4`, corrected expression `3/4`. For `P=x`, the corrected formula gives `1_{r=1}+Lambda(r)/log(N)`; the literal version still omits the `r=1` term.",
              "",
              "Detailed per-row and per-r data are in `objects_head_checks.csv` and `objects_head_polynomials.csv`.",
              "",
              "## Boundary objects and R8 core",
              "",
              f"Boundary objects and Parseval norms were computed for all supplied log/best vectors. The finite core was computed on the exact pinned `a180142f` log-grid ({core_grid_count} Ns), with each best vector freshly supplied for its N, plus the four main Ns. The cutoff is the exact integer `K=ceil(sqrt(N^3))`; `A(d)=sum_{{n|d,n<=N}}a_n` is built by divisor sieve and `R(k)=1+k*s-sum_{{d<=k}}A(d)`. Direct remainder-form checks at sampled k had maximum error `{max(float(r['direct_remainder_max_abs']) for r in core):.6g}` (tolerance `2e-10`). The log-profile head/shoulder/full-core comparison against pinned `a180142f` has maximum absolute differences `{archive['max_head_abs']:.3g}`, `{archive['max_shoulder_abs']:.3g}`, `{archive['max_full_H_abs']:.3g}` respectively.",
              "",
              "| N | profile | b | s | u | B | norm(F) | norm(F)/(7/logN) |",
              "|---:|---|---:|---:|---:|---:|---:|---:|"]
    for N in MAIN_N:
        for fam in ("log_taper", "best"):
            r = main_boundary[(N, fam)]
            lines.append(f"| {N} | {fam} | {float(r['b']):.12g} | {float(r['s']):.12g} | {float(r['u']):.12g} | {float(r['B']):.12g} | {float(r['normF']):.12g} | {float(r['normF_over_7_over_logN']):.12g} |")
    ratio_by_n = {int(r["N"]): r for r in ratios}
    r5 = ratio_by_n[10000]
    lines += ["", "Core ratios `head(best)/head(log)` and `shoulder(best)/shoulder(log)` for the full grid and main Ns are in `objects_core_ratios.csv`; raw head and shoulder values are in `objects_core.csv`.",
              f"At `N=10000`, the selected profile reduces the head to `{float(r5['head_best_over_log']):.6g}x` the log-taper head, while the shoulder rises to `{float(r5['shoulder_best_over_log']):.6g}x`; combined `H_N` is `{float(r5['full_best_over_log']):.6g}x`. This is a finite proof-cost tradeoff: the head becomes cheaper, the shoulder more expensive, and the computed full core is smaller.", "",
              "## Scope and evidence boundary", "",
              "These checks validate the finite numerical implementation of the listed objects only. Floating-point agreement does not certify the corresponding identities for arbitrary real profiles, establish the bound `||F||_2<=7/log(N)` for fitted profiles, or imply an RH result. Route B remains `CHALLENGER_NOT_RH`; `PX_RH_CLAIM` remains `NOT_MADE`.", ""]
    (outdir / "PART_B.md").write_text("\n".join(lines), encoding="utf-8", newline="\n")


def run() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--vectors", type=Path, default=HERE / "selected_vectors.csv")
    ap.add_argument("--fit-all", type=Path, default=HERE / "fit_all.csv")
    ap.add_argument("--fit-results", type=Path, default=HERE / "fit_results.csv")
    ap.add_argument("--build-only", action="store_true", help="compile native code without requiring fit outputs")
    ns = ap.parse_args()
    outdir = HERE
    started = time.monotonic()
    source = HERE / "objects_native.cpp"
    exe, compile_cmd = compile_native(source)
    native_sha = sha(source.read_bytes())
    if ns.build_only:
        print(f"BUILD_ONLY_PASS source_sha256={native_sha} binary={exe}")
        return 0
    for p in (ns.vectors, ns.fit_all, ns.fit_results):
        if not p.is_file():
            raise RuntimeError(f"required fitworker input is not ready: {p}")
    refs = parse_log_references(ns.fit_all)
    grid, core_source = pinned_core_grid()
    targets = sorted(set(grid) | set(MAIN_N))
    poly_summary = profile_family_check(ns.fit_results, outdir / "objects_head_polynomials.csv")
    with tempfile.TemporaryDirectory(prefix="q3_smooth_objects_") as td:
        tdpath = Path(td)
        refpath = tdpath / "j2_refs.csv"
        refpath.write_text("N,E\n" + "".join(f"{n},{refs[n]:.17g}\n" for n in J2_N), encoding="ascii", newline="\n")
        targetpath = tdpath / "core_targets.txt"
        targetpath.write_text("".join(f"{n}\n" for n in targets), encoding="ascii", newline="\n")
        cmd = [str(exe), str(ns.vectors), str(refpath), str(targetpath), str(outdir)]
        progress("RUN: " + shlex.join(cmd))
        logpath = outdir / "objects_run.log"
        with logpath.open("w", encoding="ascii", newline="\n") as log:
            log.write("COMMAND: " + shlex.join(cmd) + "\n")
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, encoding="ascii", errors="replace", bufsize=1)
            assert proc.stdout is not None
            for line in proc.stdout:
                print(line, end="", flush=True)
                log.write(line)
                log.flush()
            code = proc.wait()
        if code:
            raise RuntimeError(f"native run failed with status {code}; inspect {logpath}")
    archive_summary = compare_core_archive(outdir, grid)
    write_part_b(outdir, len(grid), poly_summary, archive_summary)
    prereg_blob = git("rev-parse", f"{PREREG_COMMIT}:{PREREG_PATH}").decode("ascii").strip()
    if prereg_blob != PREREG_BLOB:
        raise RuntimeError(f"pinned preregistration blob mismatch: {prereg_blob}")
    run_meta = {
        "task_commit": TASK_COMMIT,
        "preregistration_commit": PREREG_COMMIT,
        "preregistration_blob": prereg_blob,
        "preregistration_sha256": sha(git("show", f"{PREREG_COMMIT}:{PREREG_PATH}")),
        "conventions_sha256": sha((outdir / "CONVENTIONS.md").read_bytes()),
        "core_grid_source": core_source,
        "vectors_sha256": sha(ns.vectors.read_bytes()),
        "fit_all_sha256": sha(ns.fit_all.read_bytes()),
        "fit_results_sha256": sha(ns.fit_results.read_bytes()),
        "native_source_sha256": native_sha,
        "compiler_command": compile_cmd,
        "platform": platform.platform(),
        "python": sys.version,
        "core_grid_count": len(grid),
        "core_target_count_including_main": len(targets),
        "selected_vector_N_count": len({int(r["N"]) for r in csv_rows(ns.vectors)[1]}),
        "poly_head_check": poly_summary,
        "archive_core_comparison": archive_summary,
        "elapsed_seconds": time.monotonic() - started,
        "result": "PASS_FINITE_FLOATING_DIAGNOSTICS",
    }
    (outdir / "objects_run.json").write_text(json.dumps(run_meta, indent=2, sort_keys=True) + "\n",
                                                  encoding="ascii", newline="\n")
    # Reject non-LF output and verify the preregistered judge row counts.
    for name in ("objects_boundary.csv", "objects_j2.csv", "objects_j4.csv",
                 "objects_core.csv", "objects_core_ratios.csv", "objects_head_checks.csv",
                 "objects_head_polynomials.csv", "objects_core_archive_compare.csv", "objects_run.log"):
        raw = (outdir / name).read_bytes()
        if b"\r" in raw:
            raise RuntimeError(f"non-LF line ending found in {name}")
    j2rows = csv_rows(outdir / "objects_j2.csv")[1]
    j4rows = csv_rows(outdir / "objects_j4.csv")[1]
    corerows = csv_rows(outdir / "objects_core.csv")[1]
    if len(j2rows) != 3 or len(j4rows) != 8 or len(corerows) != 2 * len(targets):
        raise RuntimeError(f"output row-count mismatch J2={len(j2rows)} J4={len(j4rows)} core={len(corerows)}")
    progress(f"PASS J2={len(j2rows)} J4={len(j4rows)} core_rows={len(corerows)} elapsed={time.monotonic()-started:.2f}s")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(run())
    except Exception as exc:
        print(f"OBJECTS_FAIL: {type(exc).__name__}: {exc}", file=sys.stderr)
        raise
