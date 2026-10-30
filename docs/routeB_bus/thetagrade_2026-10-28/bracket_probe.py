"""Guarded secular parity bracket (MARKOV verdict 5.4). DIAGNOSTIC_NEVER_A_PROOF.
A = G_E, B = G_O (pole-free bulk blocks), Phi_E(t) = 1 + kappa u^T (A - t)^-1 u, Phi_O(t) = 1 - kappa v^T (B - t)^-1 v.
Bracket: alpha0 < tau < min(alpha1, beta0), Phi_E(tau) > 0, Phi_O(tau) > 0  =>  lam0(K_E) < tau < lam0(K_O) (G1a).
Question: at tau = geometric mean of lam0(K_E), lam0(K_O), are both Phi margins O(1) or as tiny as s_E, s_O?
Also scans tau over the log-window to give the interval where both Phi > 0 (in units of log10 tau).
"""
import json, sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402

mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m)
    u = mp.matrix([L / (L**2 + 16 * mp.pi**2 * a * a) for a in range(-m, m + 1)])
    v = mp.matrix([4 * mp.pi * a / (L**2 + 16 * mp.pi**2 * a * a) for a in range(-m, m + 1)])
    kap = 32 * L * mp.sinh(L / 4)**2
    G = K - kap * (u * u.T - v * v.T)
    E, O = t.parity_bases(m)
    A = E.T * G * E; B = O.T * G * O; uE = E.T * u; vO = O.T * v
    a_ev = mp.eigsy(A, eigvals_only=True); b_ev = mp.eigsy(B, eigvals_only=True)
    kE = mp.eigsy(E.T * K * E, eigvals_only=True)[0]; kO = mp.eigsy(O.T * K * O, eigvals_only=True)[0]
    I_E = mp.eye(A.rows); I_O = mp.eye(B.rows)
    PhiE = lambda x: 1 + kap * (uE.T * mp.lu_solve(A - x * I_E, uE))[0]
    PhiO = lambda x: 1 - kap * (vO.T * mp.lu_solve(B - x * I_O, vO))[0]
    tau = mp.sqrt(kE * kO)
    lo, hi = mp.log10(kE), mp.log10(min(kO, a_ev[1], b_ev[0]))
    grid = [mp.mpf(10)**(lo + (hi - lo) * k / 20) for k in range(1, 20)]
    both = [x for x in grid if PhiE(x) > 0 and PhiO(x) > 0]
    print(json.dumps({"m": m, "alpha0": mp.nstr(a_ev[0], 5), "alpha1": mp.nstr(a_ev[1], 5), "beta0": mp.nstr(b_ev[0], 5),
        "lam0_K_E": mp.nstr(kE, 5), "lam0_K_O": mp.nstr(kO, 5), "ratio_O_over_E": mp.nstr(kO / kE, 5),
        "tau": mp.nstr(tau, 5), "Phi_E_tau": mp.nstr(PhiE(tau), 5), "Phi_O_tau": mp.nstr(PhiO(tau), 5),
        "s_E": mp.nstr(PhiE(0), 5), "s_O": mp.nstr(PhiO(0), 5),
        "grid_points_both_positive": f"{len(both)}/19"}), flush=True)
