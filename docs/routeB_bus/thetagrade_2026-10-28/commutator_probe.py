"""CONFINE Q2 probe: how well does the translation mode Df_E estimate the odd bottom? DIAGNOSTIC_NEVER_A_PROOF.
g = diag(2 pi n / L) f_E (real odd vector; D f_E = i g). Exact: <g, K g> - lam_E ||g||^2 = <g, [K, N] f_E>, N = diag(2 pi n / L).
Reports lam0(K_E), lam0(K_O), Rayleigh R(g), R / lam0(K_O), the commutator term check, and where the excess of R comes from
(weights |<g, v_i>|^2 on the odd eigenvectors and their lam_i).
"""
import sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m); n = 2 * m + 1
    evE, VE = mp.eigsy(E.T * K * E); f = E * VE[:, 0]; lamE = evE[0]
    evO, VO = mp.eigsy(O.T * K * O)
    N = mp.diag([2 * mp.pi * k / L for k in range(-m, m + 1)])
    g = N * f; gg = (g.T * g)[0]
    R = (g.T * K * g)[0] / gg
    comm = (g.T * (K * N - N * K) * f)[0] / gg
    a = (O * VO).T * g; w = [a[i]**2 / gg for i in range(len(evO))]
    contrib = sorted(((w[i] * evO[i], i) for i in range(len(evO))), reverse=True)[:3]
    print(f"m={m}: lam_E={mp.nstr(lamE,4)} lam0_O={mp.nstr(evO[0],4)} R(g)={mp.nstr(R,4)} R/lam0_O={mp.nstr(R/evO[0],4)} "
          f"check R-lam_E-comm={mp.nstr(R-lamE-comm,3)} 1-w0={mp.nstr(1-w[0],3)} top excess: "
          + ", ".join(f"level {i} (lam {mp.nstr(evO[i],3)}) weight {mp.nstr(w[i],3)}" for _, i in contrib))
