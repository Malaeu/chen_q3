"""Rayleigh bound for lambda_min(E) from the CCM prolate packet k1 (cache portable_k_coeffs_lambda_sq_m_N_m.json,
real part, J-even projection as edge_ledger_relritz.q_projected_exact_even). DIAGNOSTIC_NEVER_A_PROOF."""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, "/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/thetagrade_2026-10-28")
import parity_gap_table as t
OUT = Path("/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out")
mp.mp.dps = 110
for m in [int(a) for a in sys.argv[1:]]:
    d = json.load(open(OUT / f"portable_k_coeffs_lambda_sq_{m}_N_{m}.json"))
    re = {r["n"]: mp.mpf(r["re"]) for r in d["coefficients"]}
    q = mp.matrix([(re[n] + re[-n]) / 2 for n in range(-m, m + 1)])
    q = q / mp.norm(q)
    K = t.fc.matrix_K(m)
    Eb, Ob = (lambda E, O: (E.T * K * E, O.T * K * O))(*t.parity_bases(m))
    ev, VE = mp.eigsy(Eb); mu = mp.eigsy(Ob, eigvals_only=True)[0]; lam = ev[0]
    U = (q.T * K * q)[0]
    E, _ = t.parity_bases(m); qe = E.T * q
    ov = abs((qe.T * VE[:, 0])[0]) / mp.norm(qe)
    print(json.dumps({"m": m, "lam": mp.nstr(lam, 6), "mu": mp.nstr(mu, 6), "U_k1": mp.nstr(U, 6),
        "U_over_lam": mp.nstr(U / lam, 6), "U_below_mu": bool(U < mu), "mu_over_U": mp.nstr(mu / U, 6),
        "overlap_with_ground": mp.nstr(ov, 12), "lost_norm_imag": mp.nstr(mp.sqrt(sum(mp.mpf(r['im'])**2 for r in d['coefficients'])), 4)}))
