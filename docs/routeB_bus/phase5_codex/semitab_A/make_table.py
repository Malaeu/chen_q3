import json, numpy as np, os

def load(f):
    return json.load(open(f)) if os.path.exists(f) else []

lam1 = load("rows_lam1.json"); vR = load("rows_vR.json")
thm = load("rows_theorem.json"); lams = load("rows_lambda.json")

def sgn(x, tol):
    if x is None: return "n/a"
    if abs(x) <= tol: return "~0"
    return "+" if x > 0 else "-"

lines = []
W = lines.append
W("| test | lam | \\|\\|v\\|\\|^2 | D-c_A H | prime2 | L_S | P_02 | Q(v) | N_S | E_S | N_S-E_S | rel.disc | sign E_S |")
W("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
for r in lam1+vR:
    if not r.get('representable'):
        W(f"| {r['name']} | 1 | {r['nrm2']:.6g} | {r.get('Darch', r['LS']):.6g} | {r.get('ps2', float('nan')):.6g} | {r['LS']:.6g} | "
          f"{r['P02']:.6g} | {r['Q']:.6g} | NOT REPR | NOT REPR | — | — | — |")
        continue
    for key, tag in [('src', 'F_S src'), ('pol', 'F_S pol')]:
        N = r[f'N_{key}']; E = r[f'E_{key}']; ne = N-E
        rel = abs(ne-r['LS'])/max(abs(r['LS']), 1e-12)
        W(f"| {r['name']} [{tag}] | 1 | {r['nrm2']:.6g} | {r.get('Darch', r['LS']):.6g} | {r.get('ps2', float('nan')):.6g} | {r['LS']:.6g} | "
          f"{r['P02']:.6g} | {r['Q']:.6g} | {N:.6g} | {E:.6g} | {ne:.6g} | {rel:.2e} | {sgn(E, 0.03*max(abs(E),abs(N),1e-9)+0.02)} |")
    Na = r['N_arch']; Ea = r['E_arch']; Es = r.get('E_spec_arch')
    rel = abs(Na-Ea-r.get('Darch', r['LS']))/max(abs(r.get('Darch', r['LS'])), 1e-12)
    W(f"| {r['name']} [arch S={{inf}}] | 1 | {r['nrm2']:.6g} | {r.get('Darch', r['LS']):.6g} | 0 | {r.get('Darch', r['LS']):.6g} | "
      f"{r['P02']:.6g} | {r['Q']:.6g} | {Na:.6g} | {Ea:.6g} (spec {Es:.6g}) | {Na-Ea:.6g} | {rel:.2e} | {sgn(Es,1e-9)} |")
open("table_main.md", "w").write("\n".join(lines)+"\n")

L2 = []
L2.append("| test | lambda | l=2log(lam) | L_S | E_arch(spec) | E_src | E_pol | N_arch | N_src | N_pol |")
L2.append("|---|---|---|---|---|---|---|---|---|---|")
for r in lams:
    L2.append(f"| {r['name']} | {r['lam']:.6f} | {2*np.log(r['lam']):.6f} | {r['LS']:.6g} | {r['E_spec_arch']:.6g} | "
              f"{r['E_src']:.6g} | {r['E_pol']:.6g} | {r['N_arch']:.6g} | {r['N_src']:.6g} | {r['N_pol']:.6g} |")
open("table_lambda.md", "w").write("\n".join(L2)+"\n")

L3 = []
L3.append("| test | \\|int v\\| | \\|A_+\\| | \\|A_-\\| | \\|\\|v\\|\\|^2 | L_inf | E_inf (spectral, exact) | E_inf (carrier) | N_inf | E/N (spectral) |")
L3.append("|---|---|---|---|---|---|---|---|---|---|")
for r in thm:
    L3.append(f"| {r['name']} | {r['intv']:.2e} | {r['Ap']:.2e} | {r['Am']:.2e} | {r['nrm2']:.6g} | {r['L_arch']:.7g} | "
              f"{r['E_spec']:.7g} | {r['E_arch']:.7g} | {r['N_arch']:.7g} | {r['E_spec']/r['N_arch']:+.6f} |")
open("table_theorem.md", "w").write("\n".join(L3)+"\n")
print("written", len(lam1), len(vR), len(thm), len(lams))
