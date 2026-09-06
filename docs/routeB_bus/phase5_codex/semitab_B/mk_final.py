import json, os
import numpy as np

NS = [N for N in (2048, 4096, 8192) if os.path.exists(f'ops_results_N{N}.json')]
NM = NS[-1]
D = {N: {r['test']: r for r in json.load(open(f'ops_results_N{N}.json'))} for N in NS}
ORDER = [r['test'] for r in json.load(open(f'ops_results_N{NS[0]}.json'))]
DELTA = {N: 1.0 / np.sqrt(2.0 * N) for N in NS}
UMAX = {N: np.sqrt(N / 2.0) for N in NS}


def sgn(r):
    a = r['E_S']; b = r['N_S'] - r['L']
    if abs(a) < abs(r['resid']) or (a > 0) != (b > 0):
        return "?"
    return "NEG" if a < 0 else "POS"


def tbl(tag, lam, tests=None):
    o = ("| test | \\|v\\|^2 | D(v) | prime sum | L_S | P_02 | Q(v) | N_S | E_S (direct) "
         "| N_S-E_S | abs.res | rel.res | E_impl = N_S-L_S | sign(E) | Q-N_S |\n"
         "|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|:--:|--:|\n")
    for t in (tests or ORDER):
        rec = D[NM][t]
        r = rec[f'{tag}_{lam}']
        ps = rec['prime_S'] if tag == 'semi' else 0.0
        o += (f"| {t} | {rec['norm2']:.6f} | {rec['D']:.5f} | {ps:+.6f} | {r['L']:+.6f} "
              f"| {rec['P02']:+.6f} | {rec['Q']:+.3e} | {r['N_S']:+.6f} | {r['E_S']:+.6f} "
              f"| {r['NmE']:+.6f} | {abs(r['resid']):.2e} | {r['rel']:.1e} "
              f"| {r['N_S']-r['L']:+.6f} "
              f"| **{sgn(r)}** | {rec['Q']-r['N_S']:+.3e} |\n")
    return o


def conv(tag, lam):
    o = "| test | " + " | ".join(f"N={N} (delta={DELTA[N]:.5f})" for N in NS) + " | ratio |\n"
    o += "|---|" + "--:|" * (len(NS) + 1) + "\n"
    for t in ORDER:
        v = [abs(D[N][t][f'{tag}_{lam}']['resid']) for N in NS]
        rr = v[-1] / v[-2] if len(v) > 1 and v[-2] > 0 else float('nan')
        o += f"| {t} | " + " | ".join(f"{x:.3e}" for x in v) + f" | {rr:.2f} |\n"
    return o


def econv(tag, lam):
    o = "| test | " + " | ".join(f"E_S(N={N})" for N in NS) + " | " + \
        " | ".join(f"N_S(N={N})" for N in NS) + " |\n"
    o += "|---|" + "--:|" * (2 * len(NS)) + "\n"
    for t in ORDER:
        o += (f"| {t} | " + " | ".join(f"{D[N][t][f'{tag}_{lam}']['E_S']:+.6f}" for N in NS)
              + " | " + " | ".join(f"{D[N][t][f'{tag}_{lam}']['N_S']:+.6f}" for N in NS) + " |\n")
    return o


def thm_block():
    if not os.path.exists('thm_results.json'):
        return "_(theorem control not yet available)_\n"
    R = json.load(open('thm_results.json'))
    Qd = json.load(open('thm_quad.json'))
    o = ("| test | \\|v\\|^2 | D(v) | L_inf = Q(v) | N_inf | E_inf (direct) | E_inf/N_inf "
         "| abs.res | E_impl = N_inf - L_inf | theorem (E<=0) |\n"
         "|---|--:|--:|--:|--:|--:|--:|--:|--:|:--:|\n")
    for t, d in R.items():
        k = str(max(int(x) for x in d))
        r = d[k]
        q = Qd[t]
        Ei = r['N_S'] - r['L']
        ok = ("consistent" if (r['E_S'] <= abs(r['resid']) and Ei <= 0)
              else "VIOLATED beyond error")
        o += (f"| {t} | {q['norm2']:.6f} | {q['D']:.4f} | {r['L']:+.6f} | {r['N_S']:+.6f} "
              f"| {r['E_S']:+.6f} | {r['E_S']/r['N_S']:+.4f} "
              f"| {abs(r['resid']):.2e} | {Ei:+.6f} | {ok} |\n")
    o += "\n(N-dependence)\n\n| test | " + " | ".join(
        f"E_inf(N={n})" for n in sorted({int(x) for d in R.values() for x in d})) + " |\n"
    ns = sorted({int(x) for d in R.values() for x in d})
    o += "|---|" + "--:|" * len(ns) + "\n"
    for t, d in R.items():
        o += f"| {t} | " + " | ".join(f"{d[str(n)]['E_S']:+.6f}" if str(n) in d else "-"
                                      for n in ns) + " |\n"
    return o


if __name__ == '__main__':
    import sys
    what = sys.argv[1]
    if what == 'main':
        print(tbl('semi', '1.0000'))
    elif what == 'arch':
        print(tbl('arch', '1.0000'))
    elif what == 'lam':
        print(tbl('semi', '1.4142')); print(); print(tbl('semi', '2.0000'))
    elif what == 'conv':
        print(conv('semi', '1.0000'))
    elif what == 'conva':
        print(conv('arch', '1.0000'))
    elif what == 'econv':
        print(econv('semi', '1.0000'))
    elif what == 'thm':
        print(thm_block())
