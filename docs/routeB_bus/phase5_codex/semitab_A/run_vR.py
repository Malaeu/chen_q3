import numpy as np, json, time
from run_table import ops, geom, build_A, carrier_EN, E_spec
from core import Test, D_minus_cA, prime_sum, primes_upto
import tests_family as TF
ALLP = primes_upto(200000)
if __name__ == "__main__":
    ops(800); ops(3200)
    out = []
    for R in [0.5, 1.0, 2.0]:
        fun, h = TF.vR(R); t0 = time.time()
        T = Test(fun, h, f"v_R R={R}", ngl=1500)
        rec = dict(name=f"v_R R={R}", nrm2=T.nrm2, P02=T.P02, span=2*h)
        Da = D_minus_cA(T)
        rec['LS'] = Da-prime_sum(T, (2,)); rec['Q'] = Da+T.P02-prime_sum(T, ALLP)
        rec['representable'] = bool(2*h < 0.75*8.071)
        if rec['representable']:
            res = {}
            for N in (800, 3200):
                Cc, _, _ = ops(N); A = build_A(Cc, T)
                for key in ['arch', 'src', 'pol']:
                    res[(key, N)] = carrier_EN(N, 1.0, key, T, A)
                del A
            for key in ['arch', 'src', 'pol']:
                rec[f'E_{key}'] = 2*res[(key, 3200)]['E_S']-res[(key, 800)]['E_S']
                rec[f'N_{key}'] = 2*res[(key, 3200)]['N_S']-res[(key, 800)]['N_S']
            rec['E_spec_arch'] = E_spec(1.0, T)[0]
        out.append(rec)
        print(f"R={R}: span={2*h} repr={rec['representable']} ||v||^2={T.nrm2:.6g} LS={rec['LS']:.6g} "
              f"P02={T.P02:.6g} Q={rec['Q']:.6g} E_pol={rec.get('E_pol','--')} N_pol={rec.get('N_pol','--')} "
              f"Q-N={rec.get('Q',0)-rec.get('N_pol',0) if rec['representable'] else '--'} [{time.time()-t0:.0f}s]", flush=True)
        json.dump(out, open("rows_vR.json", "w"), indent=1, default=float)
