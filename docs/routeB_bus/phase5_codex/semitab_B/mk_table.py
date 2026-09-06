import json, sys, os
import numpy as np

Ns = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [2048, 4096]
Ns = [N for N in Ns if os.path.exists(f'ops_results_N{N}.json')]
data = {N: json.load(open(f'ops_results_N{N}.json')) for N in Ns}
NM = Ns[-1]
LAMS = [('1.0000', 'lambda = 1  (T = W = 1, ell = 0)  — REFERENCE TABLE'),
        ('1.4142', 'lambda = sqrt2  (ell = log 2)'),
        ('2.0000', 'lambda = 2  (ell = 2 log 2)')]
SUPPORT_MATCHED = lambda t: ('wide' not in t) and ('v_R' not in t)

def table(tag, lam):
    o = ("| test | \\|v\\|^2 | D(v) | prime sum (S) | L_S | P_02 | Q(v) | N_S | E_S | N_S-E_S "
         "| abs.res | rel.res | sign E_S | Q-N_S |\n"
         "|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|:--:|--:|\n")
    for rec in data[NM]:
        r = rec[f'{tag}_{lam}']
        ps = rec['prime_S'] if tag == 'semi' else 0.0
        o += (f"| {rec['test']} | {rec['norm2']:.6f} | {rec['D']:.6f} | {ps:+.6f} "
              f"| {r['L']:+.6f} | {rec['P02']:+.6f} | {rec['Q']:+.4e} "
              f"| {r['N_S']:+.6f} | {r['E_S']:+.6f} | {r['NmE']:+.6f} "
              f"| {abs(r['resid']):.2e} | {r['rel']:.2e} "
              f"| {'NEG' if r['E_S'] < 0 else 'POS'} | {rec['Q']-r['N_S']:+.4e} |\n")
    return o

out = []
out.append("### Reference table — S = {infinity, 2}, lambda = 1\n")
out.append(table('semi', '1.0000'))
out.append("\n### Archimedean control S = {infinity} (exact model), lambda = 1\n")
out.append("(here L = D(v) - c_A||v||^2, no prime term)\n\n")
out.append(table('arch', '1.0000'))
for lam, name in LAMS[1:]:
    out.append(f"\n### S = {{infinity, 2}}, {name}\n")
    out.append(table('semi', lam))
print(''.join(out))
