import sys, time, json
import numpy as np
import tests
from ops import SemiLocal, theta_matrix, quantities
from quad import Quad

N = int(sys.argv[1]) if len(sys.argv) > 1 else 2048
LAMS = [1.0, np.sqrt(2.0), 2.0]
qres = json.load(open('quad_results.json'))

fam = [(n, v, a) for (n, v, a) in tests.family()] + [(n, v, a) for (n, v, a) in tests.family_extra()]

models = {}
prs = {}
for tag, sem in (('arch', False), ('semi', True)):
    t0 = time.time()
    models[tag] = SemiLocal(N, semilocal=sem)
    for lam in LAMS:
        pr = models[tag].pair(lam)
        prs[(tag, lam)] = pr
        sc = models[tag].sonin_check(pr) if N <= 4096 else {}
        print(f"   {tag} lam={lam:.4f}: nblk={len(pr['alpha'])} "
              f"chk={ {k: f'{v:.1e}' for k, v in pr['checks'].items()} } "
              f"sonin={ {k: f'{v:.2e}' for k, v in sc.items()} }", flush=True)
    print(f"   [{tag} built in {time.time()-t0:.1f}s]", flush=True)

M = models['arch'].M
rows = []
for name, v, a in fam:
    t0 = time.time()
    T = theta_matrix(M, v)
    q = qres[name]
    n2 = q['norm2']
    rec = dict(test=name, norm2=n2, D=q['D'], base=q['base'], P02=q['P02'],
               prime_S=q['prime_S'], prime_all=q['prime_all'], L_S=q['L_S'], Q=q['Q'], a=q['a'])
    for tag in ('arch', 'semi'):
        Ltarget = q['base'] if tag == 'arch' else q['L_S']
        for lam in LAMS:
            r = quantities(prs[(tag, lam)], T, n2)
            diff = r['N_S'] - r['E_S']
            rec[f'{tag}_{lam:.4f}'] = dict(
                N_S=r['N_S'], E_S=r['E_S'], NmE=diff, L=Ltarget,
                resid=diff - Ltarget,
                rel=abs(diff - Ltarget) / max(abs(Ltarget), 1e-12),
                tr_out=r['tr_out'], tr_Q=r['tr_Q'], trD=r['trD'])
    rows.append(rec)
    r1 = rec['semi_1.0000']; r0 = rec['arch_1.0000']
    print(f"{name:40s} |lam=1| arch: N={r0['N_S']:+.6f} E={r0['E_S']:+.6f} N-E={r0['NmE']:+.6f} "
          f"L={r0['L']:+.6f} rel={r0['rel']:.2e} || semi: N={r1['N_S']:+.6f} E={r1['E_S']:+.6f} "
          f"N-E={r1['NmE']:+.6f} L_S={r1['L']:+.6f} rel={r1['rel']:.2e}  [{time.time()-t0:.0f}s]",
          flush=True)
    del T
json.dump(rows, open(f'ops_results_N{N}.json', 'w'), indent=1)
