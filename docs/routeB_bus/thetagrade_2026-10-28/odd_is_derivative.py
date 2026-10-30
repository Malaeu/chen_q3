"""Model-free test: is the odd window bottom the x-derivative of the even window bottom? DIAGNOSTIC_NEVER_A_PROOF.
Both bottoms of K_m synthesized on (-L/2, L/2) (common phase); derivative of the even one taken in the mode basis
(multiply mode n by 2 pi i n / L). Reports the L2 cosine between f_O and f_E'.
"""
import sys
from pathlib import Path
import mpmath as mp
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import parity_gap_table as t  # noqa: E402
mp.mp.dps = int(sys.argv[1])
for m in [int(a) for a in sys.argv[2:]]:
    K = t.fc.matrix_K(m); L = mp.log(m); E, O = t.parity_bases(m)
    vec = {}
    for S, B in (("E", E), ("O", O)):
        ev, V = mp.eigsy(B.T * K * B); vec[S] = B * V[:, 0]
    xs = [-L / 2 + L * (k + 0.5) / 300 for k in range(300)]
    def syn(c, deriv=False):
        out = []
        for x in xs:
            out.append(sum(c[j] * (2j * mp.pi * (j - m) / L if deriv else 1) * mp.exp(2j * mp.pi * (j - m) * (x + L / 2) / L) for j in range(2 * m + 1)))
        k = max(range(len(out)), key=lambda i: abs(out[i])); ph = out[k] / abs(out[k])
        return [mp.re(y / ph) for y in out]
    fo = syn(vec["O"]); fe1 = syn(vec["E"], deriv=True)
    cos = abs(sum(a * b for a, b in zip(fo, fe1))) / mp.sqrt(sum(a * a for a in fo) * sum(b * b for b in fe1))
    print(f"m={m}: cos(f_O, f_E') = {mp.nstr(cos, 10)}   1 - cos = {mp.nstr(1 - cos, 4)}")
