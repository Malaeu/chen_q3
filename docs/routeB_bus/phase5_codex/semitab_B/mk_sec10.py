import json, os
import numpy as np

NM = 8192
ops = {r['test']: r for r in json.load(open(f'ops_results_N{NM}.json'))}
bar4 = json.load(open('bar_N4096.json'))
bar8 = json.load(open('bar_N8192.json')) if os.path.exists('bar_N8192.json') else {}
ORDER = [r['test'] for r in json.load(open(f'ops_results_N{NM}.json'))]
TRANS_REL = 3.4e-3          # measured translation defect of N_S at N=8192 (worst of the two pairs)

lines = []
lines.append("| test | Q(v) | N_S | bar(N_S) | Q - N_S | L_S | E_true = N_S - L_S | sign(E_true) | Q >= N_S ? |")
lines.append("|---|--:|--:|--:|--:|--:|--:|:--:|:--:|")
summary = {'POS': [], 'NEG': [], 'UNRES': []}
for t in ORDER:
    r = ops[t]
    s = r['semi_1.0000']
    NS, L, Q = s['N_S'], s['L'], r['Q']
    relsym = bar8[t]['rel'] if t in bar8 else bar4[t]['rel']
    bar = abs(NS) * max(relsym, TRANS_REL)
    Ei = NS - L
    if abs(Ei) > bar:
        v = '**POS**' if Ei > 0 else '**NEG**'
        key = 'POS' if Ei > 0 else 'NEG'
    else:
        v = '?'
        key = 'UNRES'
    summary[key].append(t)
    mino = ('YES' if (Q - NS) > bar else ('**NO**' if (Q - NS) < -bar else '?'))
    lines.append(f"| {t} | {Q:+.6e} | {NS:+.6f} | {bar:.2e} | {Q-NS:+.4e} | {L:+.6f} "
                 f"| {Ei:+.6f} | {v} | {mino} |")
print("\n".join(lines))
print()
print(f"* `E_true > 0` beyond the bar: {len(summary['POS'])} tests -> {summary['POS']}")
print(f"* `E_true < 0` beyond the bar: {len(summary['NEG'])} tests -> {summary['NEG']}")
print(f"* unresolved: {len(summary['UNRES'])} tests -> {summary['UNRES']}")
