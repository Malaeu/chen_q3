"""lambda = sqrt2 and 2 subset (on-grid carriers)."""
import numpy as np, json, time
from run_table import ops, geom, build_A, carrier_EN, E_spec
from core import Test, D_minus_cA, prime_sum, primes_upto
import tests_family as TF
H = TF.HALF; SH = np.log(2.0)/2; hn = H-SH
SUB = [("gauss b=0.2", TF.gauss_bump(0.2, H), H, False),
       ("2bump b=0.2 (-)", lambda x: TF.gauss_bump(0.2, hn)(x-SH)-TF.gauss_bump(0.2, hn)(x+SH), H, False),
       ("pole-null v+", TF.polebump('+')[0], TF.polebump('+')[1], False)]
GRID = {1.0: (800, 3200), np.sqrt(2.0): (784, 3136), 2.0: (800, 3200)}
if __name__ == "__main__":
    out = []
    for lam, Ns in GRID.items():
        for N in Ns: ops(N)
        for key in ['arch', 'src', 'pol']:
            g = geom(Ns[1], lam, key)
            print(f"GEOM lam={lam:.6f} {key} N={Ns[1]}: m={g['m']} rankPi={g['rankPi']} ker={g['nker']} "
                  f"nblk={g['nblk']} alpha[:6]={np.array2string(g['alpha'][:6],precision=6)}", flush=True)
        for name, fun, h, cx in SUB:
            T = Test(fun, h, name, ngl=2000, complex_=cx)
            rec = dict(lam=float(lam), name=name, nrm2=T.nrm2, P02=T.P02)
            rec['LS'] = D_minus_cA(T)-prime_sum(T, (2,))
            rec['Q'] = D_minus_cA(T)+T.P02-prime_sum(T, primes_upto(100))
            res = {}
            for N in Ns:
                Cc, _, _ = ops(N); A = build_A(Cc, T)
                for key in ['arch', 'src', 'pol']:
                    res[(key, N)] = carrier_EN(N, lam, key, T, A)
                del A
            for key in ['arch', 'src', 'pol']:
                rec[f'E_{key}'] = 2*res[(key, Ns[1])]['E_S']-res[(key, Ns[0])]['E_S']
                rec[f'N_{key}'] = 2*res[(key, Ns[1])]['N_S']-res[(key, Ns[0])]['N_S']
            rec['E_spec_arch'] = E_spec(lam, T)[0]
            out.append(rec)
            print(f"  lam={lam:.4f} {name}: LS={rec['LS']:.6g} E_arch={rec['E_arch']:.6g} "
                  f"E_spec={rec['E_spec_arch']:.6g} E_src={rec['E_src']:.6g} E_pol={rec['E_pol']:.6g} "
                  f"N_pol={rec['N_pol']:.6g}", flush=True)
            json.dump(out, open("rows_lambda.json", "w"), indent=1, default=float)
