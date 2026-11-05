"""Render audited stored results; does not rerun the experiment."""
from pathlib import Path
import json,hashlib,subprocess
import mpmath as mp
P=Path(__file__).resolve().parents[1]
mp.mp.dps=90
a=json.loads((P/'task_a.json').read_text());b=json.loads((P/'task_b.json').read_text());c=json.loads((P/'task_c.json').read_text())
def fmt(x):return mp.nstr(mp.mpf(x),7)
rows=a['rows'];r60=[r for r in rows if r['dps']==60]
assert len(rows)==32 and all(not r['gate'] and not r['shift_gate'] for r in rows)
assert all(mp.mpf(r['first_omitted_atom_value'])>mp.mpf(r['gate_budget']) for r in rows)
stability=max(abs(mp.mpf(r['arithmetic'])-mp.mpf(next(q for q in rows if q['dps']==80 and q['t']==r['t'] and q['world']==r['world'])['arithmetic'])) for r in r60)
lines=['# IDENTITY_FAILURE — fixed-Gaussian response audit','',
'DIAG only. RH_PROVED: false. This audit does not establish RH, (7.4), or a matrix growth exponent. No source identity was retuned.',
'', 'The specified finite prime sum fails every Task A gate. The omitted prime-power tail already exceeds the tolerance by a single omitted positive atom. This is a failure of the prescribed finite-sum instrument to check the full-line identity; it is **not evidence against Proshka’s full-line normalization**. That normalization remains unconfirmed by this gate.',
'', 'Preregistration was committed before all numerical runs at `8e0e8da16bd0489777f3221455b854647f65b71f`. `preregistration.bundle` preserves that commit and its PREDICTIONS.md bytes. The final delivery amends that local commit to meet the single-commit request. Base `5a409f1e88439d12c5d84126e09d421781d24e26`; verdict commit `62f782316d2ba4f83d27db82d0b64e1e8361cad2`, blob `2b5e02a0aa816da34c204f2a56a9033e6ac6b542`. Exact verdict bytes are in SOURCE_VERDICT.md. Input Git blobs were verified against the request.',
'', '## Task A', '',
'Both precisions, both worlds, all eight t: **32/32 IDENTITY_FAILURE**. Full H, S, both sides, quartet terms, tolerances, omitted atom, perturbation and cancellation ratios are in `task_a.json`. Table values below use dps60; all dps80 decisions agree. Maximum absolute arithmetic change on the repeat: '+fmt(stability)+'.', '',
'| t | zeta arithmetic − zero | zeta cancellation ratio | plant cancellation ratio | gate 60 / 80 (both worlds) |',
'|---:|---:|---:|---:|:---|']
for r in r60:
 if r['world']!='zeta':continue
 p=next(q for q in r60 if q['world']=='plant' and q['t']==r['t'])
 lines.append('| '+ ' | '.join([r['t'],fmt(r['difference']),fmt(r['cancellation_ratio_zero']),fmt(p['cancellation_ratio_zero']),'FAIL / FAIL'])+' |')
lines+=['', 'Cancellation ratio uses (|H|+|S|)/|h_zero|; JSON also supplies the misleadingly smaller truncated-arithmetic ratio. No modulus square is substituted for F(u)^2. The quartet arithmetic moments are computed independently by full-line quadrature of g; the zero side uses F. Its polarized form is 2 Re(F(u)^2(e^{ut}+e^{-ut})), matching the builder’s 4 Re(ccᵀ) on the even sector.', '',
'The cutoff is exactly floor(exp(t+9)). C(v) has polynomial v^8−28.5v^6+217.5625v^4−442.875v²+112.6875, times exp(−v²/2)/sqrt(2π). It is positive for |v|≥9, so every omitted prime-power term is positive. Every row’s first omitted atom alone exceeds its gate budget. The observed residual is consistent with this omitted tail; it was not subtracted from the gate.', '',
'The zero tail uses Nζ(T)≤T² for T≥60, a loose consequence of classical explicit Riemann–von Mangoldt counting bounds (e.g. Rosser, “Explicit bounds for some functions of prime numbers”, 1941). For each integer shell k≥60, use 2(k+1)² times (k²+1/4)²(k²+1/2)² exp(1/8−k²/2+t/2). The polynomial times Gaussian decreases on these shells; the remaining shell sum past100 is dominated by the recorded factor 1.0000000001. The uniform bound for t≤6 is '+fmt(max(mp.mpf(r['zero_tail_bound']) for r in rows))+'. This is an analytic tail bound evaluated numerically, not an interval enclosure of the quadrature.', '',
'Changing c_* by +1e−30 changes arithmetic by −1e−30 C(t). All 32 perturbed gates fail. Its isolated change exceeds the gate budget by at least '+fmt(min(abs(mp.mpf(r['shift_delta']))/mp.mpf(r['gate_budget']) for r in rows))+'. The already failed baseline means this plant is **not a clean pass-to-fail validation**; the perturbation is masked by the much larger cutoff omission.', '',
'## Task B', '',
'Unnormalized w_m from (6.1), as requested; these q values are not the graph-unit q in (6.5). The reference 2W[g]+2h(log m/2) is evaluated from the absolutely convergent zero formula for comparison only; all computed window forms retain literal arithmetic, Gamma tail and poles. This reference use does not turn the failed Task A gate into a pass.', '',
'Components telescope as W[chi f]−W[f], W[P chi f]−W[chi f], the e0 correction, then the e1 correction. Values are signed. Projection residuals near 1e−12 reflect the numerical resolution.', '',
'| world | m | return error | chi | cosine projection | e0 | e1 |', '|:---|---:|---:|---:|---:|---:|---:|']
for r in b['rows']:lines.append('| '+' | '.join([r['world'],str(r['m'])]+[fmt(r[k]) for k in ['return_error','chi_component','cosine_projection_component','e0_component','e1_component']])+' |')
lines+=['','Fresh pinned 256-bit arithmetic matrices are used for m≤300; function-level finite-cosine correlation W is used above300. At300 the largest crosscheck discrepancy is '+fmt(next(x['max_abs_difference'] for x in b['crosschecks'] if x['m']==300))+'. Across all three crosschecks the maximum is '+fmt(max(x['max_abs_difference'] for x in b['crosschecks']))+'. FFT-size and cutoff-quadrature repeats and integration error estimates are recorded. Results are numerical DIAG, not interval certificates.', '',
'The bound crosses1e−30 at L=363.8803637220 (zeta) and363.9726782972 (plant); it is strictly below for larger L. First integer L=364. Explicit bound derivation and constants are in `task_b_notes.md`; the same bound is consumed in Task C. Its purpose is a conservative regime map, not a useful error estimate at these finite m.', '',
'## Task C', '',
'The table uses the declared magnitude envelope for the total on-line response, with zero-tail allowance, plus the explicit return-error bound. Thus it is an envelope visibility threshold; it does not certify an actual oscillatory negative response at m*. The DH entries use the supplied numerical census and the specified Task B comparison budget; this is not a separately computed DH literal window bound. See `task_c_notes.md` for tail counting and scope. Log means natural log.', '',
'| world / pair | sigma_right | gamma | log(m*) envelope crossing |', '|:---|---:|---:|---:|']
for r in c['rows']:lines.append('| '+' | '.join([r['world']+' '+str(r['index']),fmt(r['sigma_right']),fmt(r['gamma']),fmt(r['log_m_star']) if r['log_m_star'] else 'unavailable'])+' |')
lines+=['', 'Crossings are continuous L values. The formal smallest integer is floor(exp(L_cross))+1 (subject to m≥3); its exact giant integer is not constructed or claimed from rounded L. JSON records rounding-scale information. The table assumes census completeness as supplied; the census itself is numerical, not certified. Dominating an envelope is stronger than dominating the phase-dependent absolute sum; no smallest crossing of that oscillatory sum is claimed.', '',
'## Reproduce and verify', '',
'From repository root: run `python docs/routeB_bus/prove_rh_response_audit_2026-11-05/scripts/task_a.py`, then task_b.py, task_c.py `--bound explicit`, and report.py. Dependencies: Python, mpmath, NumPy, SciPy; pinned matrix checks also require gmpy2 and python-flint. Preserve the preregistration before any rerun. SHA256SUMS covers all delivered artifacts except itself. Source and raw results remain unchanged after the reported failure.', '',
'AUTOPSY: dropped=NUMERICAL_SURROGATE; note=finite prime cutoff cannot resolve this full-line response at the prescribed gate; no RH sign or normalization conclusion is admitted.', '']
(P/'RESULT.md').write_text('\n'.join(lines))
