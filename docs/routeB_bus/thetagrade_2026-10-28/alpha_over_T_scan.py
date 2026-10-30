"""Smoothness of alpha/T on consecutive diagonal cells m = N. DIAGNOSTIC_NEVER_A_PROOF.

alpha_m = kappa(ground) - kappa_Xi, T_m = (L^2/4 pi^2) sum_{k>N} 1/k^2 (as in r2_second_jet / RATE verdict).
Question (owner 29.10, "Perelman entropy"): is alpha/T ~ 0.35 a smooth law, or does it jump at primes m
(arithmetic = zeros via the explicit formula)? Uses r2_second_jet.ground_full (flint arb, same as 04.09).
"""
import json, math, sys, time
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "phase5_codex"))
sys.path.insert(0, str(HERE.parent / "phase5_scripts"))
from r2_second_jet import ground_full, kappa_full, KAPPA_X  # noqa: E402

out = Path(sys.argv[1]); ms = [int(a) for a in sys.argv[2:]]
for m in ms:
    t0 = time.time(); dps = max(400, int(9 * m))
    c, L = ground_full(m, m, dps)
    T = (L * L / (4 * math.pi ** 2)) * (math.pi ** 2 / 6 - sum(1 / (k * k) for k in range(1, m + 1)))
    kG = kappa_full(c, L); a = kG - KAPPA_X
    row = {"m": m, "dps": dps, "L": L, "kappa_G": kG, "alpha": a, "T": T, "alpha_over_T": a / T,
           "is_prime": all(m % d for d in range(2, int(m ** 0.5) + 1)), "seconds": round(time.time() - t0, 1)}
    with out.open("a") as f: f.write(json.dumps(row) + "\n")
    print(json.dumps(row), flush=True)
