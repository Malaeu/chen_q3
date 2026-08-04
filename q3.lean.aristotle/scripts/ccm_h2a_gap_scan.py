#!/usr/bin/env python3
"""CCM H2a Layer-3 gap-scan discriminator (FIT_NOT_LAW, binary64, NOT proof tree).

Measures the two spectral gaps of the finite CCM Weil matrix across a grid of
cells (m, N) and fits their decay law, to decide whether H2a "Layer 3" is
engineering (delta ~ poly(lambda)) or an alpha-class safe (delta ~ exp(-c*lambda^2)).

Object identity is preserved by REUSING the certified Arb entry builders from
`ccm_h2a_sector_cell_13_2_arb.py` (contract point 1). Only the prime-sum RANGE is
lifted from the hardcoded 13 to the cell modulus m. Spectra come from the
generalized pencil (K, G) via scipy.linalg.eigh (contract point 2). A built-in
judge reproduces the certified (13, 2) fact before scanning (point 3), and a
Prime-sign-flip plant proves the scan is coupled to the object (point 4).

Diagnostic only: class FIT_NOT_LAW, IEEE-754 binary64, in_proof_tree=false (K7).
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import sys
from pathlib import Path

import numpy as np
import scipy.linalg as sla
from flint import arb, ctx

# --- FIX-3: fail-closed source identity guard (sha256 must match certified bytes) ---
SOURCE_PATH = Path(__file__).resolve().parent / "ccm_h2a_sector_cell_13_2_arb.py"
SOURCE_SHA256 = "01464c9b47b415fb85480b6aaea18b469c0cd659f18417ead3768e79c71aba72"

# Certified (13, 2) witnesses (source lines 79-84): mu = 1e-7, mu+delta = 4e-7.
MU = 1e-7
THRESHOLD = 4e-7  # mu + delta

# FIX-6: grid with composites to decorrelate Lambda(m) jumps from log m.
GRID_M = (5, 6, 7, 9, 11, 12, 13, 16, 17, 19, 21, 23, 24)
GRID_N = (1, 2, 3, 4)


def load_source():
    """Load the certified (13,2) module after a fail-closed SHA-256 check (FIX-3)."""
    actual = hashlib.sha256(SOURCE_PATH.read_bytes()).hexdigest()
    if actual != SOURCE_SHA256:
        print(
            f"H2A_GAP_SCAN_SOURCE_HASH_MISMATCH expected={SOURCE_SHA256} actual={actual}",
            file=sys.stderr,
        )
        sys.exit(2)
    spec = importlib.util.spec_from_file_location("ccm_cell_13_2_src", SOURCE_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # runs the source's own flint guard; STOP if flint absent
    return mod


# --- generalized sector embeddings (verified against N=2 source lines 86-101) ---
def modes(N: int) -> list[int]:
    return list(range(-N, N + 1))


def uplus(N: int) -> np.ndarray:
    md = modes(N)
    U = np.zeros((2 * N + 1, N + 1))
    for i, mode in enumerate(md):
        U[i, abs(mode)] = 1.0
    return U


def uminus(N: int) -> np.ndarray:
    md = modes(N)
    U = np.zeros((2 * N + 1, N))
    for i, mode in enumerate(md):
        if mode != 0:
            U[i, abs(mode) - 1] = 1.0 if mode > 0 else -1.0
    return U


def gplus(N: int) -> np.ndarray:
    d = np.full(N + 1, 2.0)
    d[0] = 1.0
    return np.diag(d)


def gminus(N: int) -> np.ndarray:
    return np.diag(np.full(N, 2.0))


# --- entry object: REUSE source builders; only lift the prime RANGE (13 -> m_project) ---
def prime_generic(length, n, m, m_project, mod):
    """Byte-faithful copy of source prime_entry (lines 359-366) with 13 -> m_project."""
    total = arb(0)
    for k, p in mod.von_mangoldt_support(m_project):
        x = length if k == m_project else arb(k).log()
        q_value = mod.q_kernel(x, length, n, m)
        if not q_value.imag.contains(0):
            print("H2A_GAP_SCAN_PRIME_IMAG_NONZERO", file=sys.stderr)
            sys.exit(5)
        total += arb(p).log() / arb(k).sqrt() * q_value.real
    return total


def weil_entry_generic(length, n, m, m_project, prime_sign, precision, mod):
    """tau = W02 - WR - prime_sign * Prime; W02/WR reused verbatim from source."""
    return (
        mod.w02_entry(length, n, m)
        - mod.wr_entry(length, n, m, precision)
        - prime_sign * prime_generic(length, n, m, m_project, mod)
    )


def _midf(x) -> float:
    """Arb ball -> float64 midpoint."""
    try:
        return float(x.mid())
    except (AttributeError, TypeError):
        return float(x)


def build_T(m_project: int, N: int, prime_sign: int, precision: int, mod) -> np.ndarray:
    ctx.prec = precision
    length = arb(m_project).log()
    md = modes(N)
    size = 2 * N + 1
    T = np.zeros((size, size))
    for i in range(size):
        for j in range(i, size):
            val = _midf(
                weil_entry_generic(length, md[i], md[j], m_project, prime_sign, precision, mod)
            )
            T[i, j] = val
            T[j, i] = val
    return T


def sector_eigs(T: np.ndarray, N: int):
    Up, Um = uplus(N), uminus(N)
    Kp = Up.T @ T @ Up
    Km = Um.T @ T @ Um
    wp = sla.eigh(Kp, gplus(N), eigvals_only=True)  # ascending
    wm = sla.eigh(Km, gminus(N), eigvals_only=True)
    return np.sort(wp), np.sort(wm)


def gaps_for_cell(m_project: int, N: int, prime_sign: int, precision: int, mod) -> dict:
    T = build_T(m_project, N, prime_sign, precision, mod)
    wp, wm = sector_eigs(T, N)
    eps_p1 = float(wp[0])
    eps_p2 = float(wp[1])  # Kp is (N+1)x(N+1), N>=1 => at least 2x2
    eps_m1 = float(wm[0])
    return {
        "m": m_project,
        "N": N,
        "eps_p1": eps_p1,
        "eps_p2": eps_p2,
        "eps_m1": eps_m1,
        "d_plus": eps_p2 - eps_p1,   # simplicity gap
        "d_cross": eps_m1 - eps_p1,  # parity gap
    }


# --- FIX-1: judge tests EXACTLY the certified fact, no eps_p1>0 clause ---
def judge_13_2(mod, precision: int) -> dict:
    g = gaps_for_cell(13, 2, +1, precision, mod)
    ok = (g["eps_p1"] < MU) and (g["eps_p2"] > THRESHOLD) and (g["eps_m1"] > THRESHOLD)
    if not ok:
        print(
            "H2A_GAP_SCAN_JUDGE_FAILED_13_2 "
            f"eps_p1={g['eps_p1']:.3e} eps_p2={g['eps_p2']:.3e} eps_m1={g['eps_m1']:.3e}",
            file=sys.stderr,
        )
        sys.exit(3)
    # Sign of eps_p1 is NOT certified -> registered observation (Weil-form positivity on the cell).
    g["eps_p1_sign_observation"] = "positive" if g["eps_p1"] > 0 else ("zero" if g["eps_p1"] == 0 else "negative")
    return g


# --- FIX-4: micro-plant on the prime-RANGE generalization (judge only covers m=13) ---
def range_microplant(mod) -> None:
    support5 = sorted(k for k, _ in mod.von_mangoldt_support(5))
    if support5 != [2, 3, 4, 5]:
        print(f"H2A_GAP_SCAN_RANGE_MICROPLANT_FAILED von_mangoldt_support(5)={support5}", file=sys.stderr)
        sys.exit(4)
    # cross-check: sum of Lambda(n) for n<=m equals log lcm(1..m); check m in {5,23}
    for mm in (5, 23):
        lam = sum(math.log(p) for k, p in mod.von_mangoldt_support(mm))
        lcm = 1
        for n in range(1, mm + 1):
            lcm = lcm * n // math.gcd(lcm, n)
        if abs(lam - math.log(lcm)) > 1e-9:
            print(f"H2A_GAP_SCAN_RANGE_MICROPLANT_LCM_FAILED m={mm}", file=sys.stderr)
            sys.exit(4)


# --- point 4: object plant self-test (Prime sign flip must change the spectrum) ---
def plant_selftest(mod, precision: int) -> None:
    g_pos = gaps_for_cell(13, 2, +1, precision, mod)
    g_neg = gaps_for_cell(13, 2, -1, precision, mod)
    triple_pos = (g_pos["eps_p1"], g_pos["eps_p2"], g_pos["eps_m1"])
    triple_neg = (g_neg["eps_p1"], g_neg["eps_p2"], g_neg["eps_m1"])
    if all(abs(a - b) < 1e-15 for a, b in zip(triple_pos, triple_neg)):
        print("H2A_GAP_SCAN_PLANT_INSENSITIVE", file=sys.stderr)
        sys.exit(4)
    # +1 must pass the certified judge; -1 must NOT (spectrum genuinely moved)
    neg_passes = (g_neg["eps_p1"] < MU) and (g_neg["eps_p2"] > THRESHOLD) and (g_neg["eps_m1"] > THRESHOLD)
    if neg_passes:
        print("H2A_GAP_SCAN_PLANT_FLIP_STILL_CERTIFIES", file=sys.stderr)
        sys.exit(4)


# --- FIX-2 + FIX-5: fits per N (no pooling), lambda^2 = m, extra outcome NO_DECAY ---
def _linfit(x, y):
    """Return (slope, intercept, R2) of y ~ slope*x + intercept."""
    x = np.asarray(x, float)
    y = np.asarray(y, float)
    if len(x) < 2:
        return float("nan"), float("nan"), float("nan")
    slope, intercept = np.polyfit(x, y, 1)
    yhat = slope * x + intercept
    ss_res = float(np.sum((y - yhat) ** 2))
    ss_tot = float(np.sum((y - np.mean(y)) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    return float(slope), float(intercept), float(r2)


def fit_laws(records: list[dict]) -> dict:
    """Per-N regressions of ln(d_plus) and ln(d_cross). lambda^2 = m (FIX-2)."""
    out = {"per_N": {}, "findings": []}
    for N in sorted({r["N"] for r in records}):
        rows = [r for r in records if r["N"] == N]
        rows.sort(key=lambda r: r["m"])
        block = {}
        for gapname in ("d_plus", "d_cross"):
            usable = [r for r in rows if r[gapname] > 0]
            for r in rows:
                if r[gapname] <= 0:  # FIX-5c: delta<=0 is a FINDING, not a failure
                    out["findings"].append(
                        f"ORDERING_REFUTED_ON_CELL m={r['m']} N={r['N']} {gapname}={r[gapname]:.3e}"
                    )
            if len(usable) < 2:
                block[gapname] = {"n_points": len(usable), "note": "insufficient positive points"}
                continue
            m_vals = [r["m"] for r in usable]                 # lambda^2 = m
            lnm = [math.log(r["m"]) for r in usable]          # ln lambda^2 = ln m ; poly slope = -p/2
            lnlogm = [math.log(math.log(r["m"])) for r in usable]  # optional: poly in L
            lnd = [math.log(r[gapname]) for r in usable]
            s_exp, _, r2_exp = _linfit(m_vals, lnd)     # safe: ln d vs m, slope = -c
            s_poly, _, r2_poly = _linfit(lnm, lnd)      # poly: ln d vs ln m, slope = -p/2
            s_polyL, _, r2_polyL = _linfit(lnlogm, lnd)  # poly-in-L (optional)
            block[gapname] = {
                "n_points": len(usable),
                "exp_law": {"c": -s_exp, "R2": r2_exp},          # d ~ exp(-c*m)
                "poly_law": {"p": -2 * s_poly, "R2": r2_poly},   # d ~ m^(-p/2) = lambda^(-p)
                "poly_in_L": {"slope": s_polyL, "R2": r2_polyL},
            }
        out["per_N"][N] = block
    return out


def verdict(fits: dict) -> str:
    """Verdict on the leading gap d_plus, by consistency across N (FIX-5)."""
    votes = []
    for N, block in fits["per_N"].items():
        b = block.get("d_plus")
        if not b or "exp_law" not in b:
            continue
        c = b["exp_law"]["c"]
        r2e = b["exp_law"]["R2"]
        r2p = b["poly_law"]["R2"]
        # slopes >= 0 means the gap does not decay -> GAP_PERSISTENT (best for engineering)
        exp_slope = -c  # ln d vs m slope
        poly_slope = -b["poly_law"]["p"] / 2  # ln d vs ln m slope
        if exp_slope >= 0 and poly_slope >= 0:
            votes.append("GAP_PERSISTENT")
        elif (r2e - r2p) > 0.05 and c > 0:
            votes.append("SAFE")
        elif (r2p - r2e) > 0.05:
            votes.append("ENGINEERING")
        else:
            votes.append("AMBIGUOUS")
    if not votes:
        return "NO_FIT"
    # consistency across N
    uniq = set(votes)
    if uniq == {"GAP_PERSISTENT"}:
        return "GAP_PERSISTENT (engineering)"
    if uniq <= {"SAFE"}:
        return "SAFE (alpha-class RH core)"
    if uniq <= {"ENGINEERING", "GAP_PERSISTENT"}:
        return "ENGINEERING (Layer-3; B/C mechanisms live)"
    if uniq <= {"SAFE", "AMBIGUOUS"}:
        return "SAFE-leaning (needs finer grid)"
    return f"MIXED across N {sorted(uniq)} -> AMBIGUOUS (needs finer grid)"


def format_table(records: list[dict]) -> str:
    hdr = f"{'m':>3} {'N':>2} {'eps_p1':>13} {'eps_p2':>13} {'eps_m1':>13} {'d_plus':>13} {'d_cross':>13}"
    lines = [hdr, "-" * len(hdr)]
    for r in sorted(records, key=lambda x: (x["N"], x["m"])):
        lines.append(
            f"{r['m']:>3} {r['N']:>2} {r['eps_p1']:>13.5e} {r['eps_p2']:>13.5e} "
            f"{r['eps_m1']:>13.5e} {r['d_plus']:>13.5e} {r['d_cross']:>13.5e}"
        )
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description="CCM H2a Layer-3 gap-scan discriminator (FIT_NOT_LAW)")
    ap.add_argument("--precision", type=int, default=100, help="Arb working precision in BITS (FIX-6)")
    ap.add_argument("--plant-prime-flip", action="store_true", help="scan the mutated (Prime-flipped) object")
    ap.add_argument("--json", type=str, default=None, help="optional JSON dump path")
    args = ap.parse_args()

    mod = load_source()  # FIX-3 SHA guard + source flint guard
    ctx.prec = args.precision

    # --- gates (must all pass before the grid) ---
    range_microplant(mod)              # FIX-4
    plant_selftest(mod, args.precision)  # contract point 4
    j = judge_13_2(mod, args.precision)  # FIX-1
    print(f"[gate] source SHA ok | range micro-plant ok | Prime-flip plant ok | (13,2) judge CERTIFIED")
    print(f"[gate] (13,2): eps_p1={j['eps_p1']:.5e} eps_p2={j['eps_p2']:.5e} eps_m1={j['eps_m1']:.5e} "
          f"| eps_p1 sign = {j['eps_p1_sign_observation']} (registered observation, NOT certified)\n")

    prime_sign = -1 if args.plant_prime_flip else +1
    if args.plant_prime_flip:
        print("[MODE] --plant-prime-flip: scanning the MUTATED object (Prime sign flipped)\n")

    records = []
    for N in GRID_N:
        for m in GRID_M:
            records.append(gaps_for_cell(m, N, prime_sign, args.precision, mod))

    print(format_table(records))
    fits = fit_laws(records)
    print("\n=== fits per N (lambda^2 = m; safe: ln d_plus vs m, slope=-c | poly: ln d_plus vs ln m) ===")
    for N in sorted(fits["per_N"]):
        b = fits["per_N"][N].get("d_plus", {})
        if "exp_law" in b:
            print(f"  N={N}: exp c={b['exp_law']['c']:+.4e} R2={b['exp_law']['R2']:.4f} | "
                  f"poly p={b['poly_law']['p']:+.4f} R2={b['poly_law']['R2']:.4f} | n={b['n_points']}")
        else:
            print(f"  N={N}: d_plus fit skipped ({b.get('note','')})")
    if fits["findings"]:
        print("\n=== FINDINGS (delta<=0 on a cell = ordering refuted, reported not asserted) ===")
        for f in fits["findings"]:
            print("  " + f)

    v = verdict(fits)
    print(f"\n=== VERDICT (leading gap d_plus, by N-consistency): {v} ===")
    print("class=FIT_NOT_LAW arithmetic=IEEE754_BINARY64 in_proof_tree=false K7 | "
          "no route promotion | RH not claimed | Bus 010 VOID")

    if args.json:
        payload = {
            "class": "FIT_NOT_LAW",
            "arithmetic": "IEEE754_BINARY64",
            "in_proof_tree": False,
            "precision_bits": args.precision,
            "prime_sign": prime_sign,
            "lambda2_axis": "m",
            "grid_m": list(GRID_M),
            "grid_N": list(GRID_N),
            "judge_13_2": {k: j[k] for k in ("eps_p1", "eps_p2", "eps_m1", "eps_p1_sign_observation")},
            "records": records,
            "fits": fits,
            "verdict": v,
        }
        outp = Path(args.json)
        outp.parent.mkdir(parents=True, exist_ok=True)
        outp.write_text(json.dumps(payload, indent=2))
        print(f"\n[json] {outp}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
