import numpy as np, json, time
from core import Test, D_minus_cA, prime_sum, primes_upto
from run_table import ops, geom, build_A, carrier_EN, E_spec
import theorem_ctrl as TC

HB = np.log(2.0)/2
CASES = [("thm A: h=0.3466 centered", lambda x: TC.wfun(x, HB), HB, False),
         ("thm B: h=0.25 centered",   lambda x: TC.wfun(x, 0.25), 0.25, False),
         ("thm C: h=0.15 @ +0.19",    lambda x: TC.wfun(x, 0.15, 0.19), HB, False),
         ("thm D: h=0.15 @ -0.19",    lambda x: TC.wfun(x, 0.15, -0.19), HB, False),
         ("thm E: two-bump (+)",      lambda x: TC.wfun(x, 0.15, 0.19)+TC.wfun(x, 0.15, -0.19), HB, False),
         ("thm F: complex h=.15 +/-", lambda x: TC.wfun(x, 0.15, 0.19)+1j*TC.wfun(x, 0.15, -0.19), HB, True)]
if __name__ == "__main__":
    ops(800); ops(3200)
    rows = []
    for name, fun, h, cx in CASES:
        T = Test(fun, h, name, ngl=2000, complex_=cx)
        nv = T.nrm2
        i0 = complex(np.sum(T.w*T.v))
        rec = dict(name=name, nrm2=nv, intv=abs(i0), Ap=abs(T.Ap), Am=abs(T.Am), P02=T.P02)
        rec['L_arch'] = D_minus_cA(T)
        rec['LS'] = rec['L_arch']-prime_sum(T, (2,))
        rec['Q'] = rec['L_arch']+T.P02-prime_sum(T, primes_upto(100))
        res = {}
        for N in (800, 3200):
            Cc, _, _ = ops(N); A = build_A(Cc, T)
            res[N] = carrier_EN(N, 1.0, 'arch', T, A); del A
        rec['E_arch'] = 2*res[3200]['E_S']-res[800]['E_S']
        rec['N_arch'] = 2*res[3200]['N_S']-res[800]['N_S']
        rec['E_raw'] = [res[800]['E_S'], res[3200]['E_S']]
        rec['N_raw'] = [res[800]['N_S'], res[3200]['N_S']]
        rec['E_spec'], _ = E_spec(1.0, T)
        rec['ratio'] = rec['E_arch']/rec['N_arch'] if rec['N_arch'] != 0 else None
        rows.append(rec)
        print(f"{name}: |int v|={rec['intv']:.2e} |A+|={rec['Ap']:.2e} |A-|={rec['Am']:.2e} ||v||^2={nv:.6g}\n"
              f"    L_arch={rec['L_arch']:.8g}  E_spec={rec['E_spec']:.8g}  E_carrier={rec['E_arch']:.8g}"
              f"  N={rec['N_arch']:.6g}  E/N={rec['ratio']:.6g}", flush=True)
        json.dump(rows, open("rows_theorem.json", "w"), indent=1, default=float)
