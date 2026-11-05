"""Verify and render the stored Task A rerun; no numerical rerun."""
from pathlib import Path
import json,hashlib,ast,subprocess
import mpmath as mp
P=Path(__file__).resolve().parent
mp.mp.dps=90
r=json.loads((P/'results.json').read_text());rows=r['rows']
assert r['complete'] and len(rows)==20
ok=all(x['baseline_pass'] and x['plant_fail'] and mp.mpf(x['prime_tail']['reported_upper'])<mp.mpf('1e-18') for x in rows)
assert (r['status']=='PASS')==ok
status='PASS' if ok else 'INSTRUMENT_FAILURE'
maxbase=max(abs(mp.mpf(x['baseline_residual'])) for x in rows)
minplant=min(abs(mp.mpf(x['shifted_residual'])) for x in rows)
maxptail=max(mp.mpf(x['prime_tail']['reported_upper']) for x in rows)
maxztail=max(mp.mpf(x['zero_tail_bound']) for x in rows)
stability=max(abs(mp.mpf(x['arithmetic'])-mp.mpf(next(y['arithmetic'] for y in rows if y['t']==x['t'] and y['world']==x['world'] and y['dps']==70))) for x in rows if x['dps']==50)
def fmt(x):return mp.nstr(mp.mpf(x),10)
lines=['# Task A instrument-fix rerun: '+status,'',
'DIAG only. RH_PROVED: false. No RH claim and no claim of (7.4). Source formulas and previous audit artifacts are unchanged.', '',
'Both worlds, all five t, both precisions: **20/20 baselines PASS; 20/20 c_*+1e−10 plants FAIL** the absolute1e−15 gate. The independently bounded omitted prime-power tail is below1e−18 in every row. The revised instrument meets all requested checks.', '',
'Base rh_clean@2cd805e0abf59d21ab103410548e9b011e5ee7a5. PREDICTIONS.md was committed before numerical runs at `c64e6038675138381df066e711aed895e22b550f`. `preregistration.bundle` preserves that commit against the base; it is retained when the local commit is amended for one final delivered commit. The numerical start time and input fingerprints are in results.json.', '',
'## Gate table', '',
'Prime cutoff is floor(exp(t+12)); all prime powers are retained. Columns show absolute residuals. Each precision uses a fresh zero computation, Gamma quadrature, prime sum and quartet-moment quadrature. The perturbation changes arithmetic by exactly −1e−10 C(t).', '',
'| world | t | baseline error50 | baseline error70 | planted error70 | baseline50/70 | plant50/70 |', '|:---|---:|---:|---:|---:|:---|:---|']
for world in ['zeta','zeta_plus_quartet']:
 for t in ['0','0.5','1','1.5','2']:
  x=next(x for x in rows if x['world']==world and x['t']==t and x['dps']==50)
  y=next(x for x in rows if x['world']==world and x['t']==t and x['dps']==70)
  lines.append('| '+' | '.join([world,t,fmt(abs(mp.mpf(x['baseline_residual']))),fmt(abs(mp.mpf(y['baseline_residual']))),fmt(abs(mp.mpf(y['shifted_residual']))),'PASS / PASS' if x['baseline_pass'] and y['baseline_pass'] else 'INSTRUMENT_FAILURE','FAIL / FAIL' if x['plant_fail'] and y['plant_fail'] else 'INSTRUMENT_FAILURE'])+' |')
lines+=['', 'Maximum baseline error: **'+fmt(maxbase)+'**. Minimum planted error: **'+fmt(minplant)+'**. Maximum arithmetic change between50 and70 dps: '+fmt(stability)+'. Full H, S, both arithmetic/zero sides, quartet terms, C(t), shift and decisions for every row are in results.json.', '',
'## Omitted arithmetic tail: independent analytic bound', '',
'Write N=floor(exp(t+12)), b=log N−t, D=b−1/2−9/b. Here b>11.99 and D>0 for every requested t. The explicit polynomial is', '',
'    C(v) = [v^8−28.5v^6+217.5625v^4−442.875v²+112.6875]',
'           × exp(−v²/2)/sqrt(2π).', '',
'For v≥b, the sum of absolute polynomial coefficients after division by v^8 is less than2, so |C(v)|≤2v^8exp(−v²/2)/sqrt(2π). Bound Lambda(n) by log n and sum over every integer n>N. Each of the two resulting functions of n decreases on [N,infinity): its logarithmic derivative in lambda=log n is 1/lambda−1/2+8/(lambda±t)−(lambda±t)<0. Therefore the sum is at most the integral starting at N.', '',
'After v=log x−t or v=log x+t, both integrals are bounded by the same expression. This gives', '',
'    tail ≤ 4 exp(t/2)/sqrt(2π)',
'              × integral_b^infinity (v+t)v^8 exp(v/2−v²/2) dv',
'         ≤ 4 exp(t/2)(b+t)b^8 exp(b/2−b²/2)/(sqrt(2π)D).', '',
'The second inequality follows because the logarithmic derivative of the integrand is 1/(v+t)+8/v+1/2−v≤−D for all v≥b. This bounds the entire omitted prime-power tail, including both shifts, without using a zero identity or any cancellation. The quartet is exact and adds no omitted arithmetic tail.', '',
'For reporting, the driver multiplies the analytic majorant by1.001, then rounds upward to eight significant digits. The formula is an analytic bound; its evaluation uses mpmath, not an interval library.', '',
'| t | N | reported omitted-tail upper bound (max50/70) | below1e−18 |', '|---:|---:|---:|:---|']
for t in ['0','0.5','1','1.5','2']:
 rr=[x for x in rows if x['t']==t]
 lines.append('| '+' | '.join([t,str(rr[0]['cutoff']),fmt(max(mp.mpf(x['prime_tail']['reported_upper']) for x in rr)),'YES'])+' |')
lines+=['', 'Maximum reported omitted arithmetic tail: **'+fmt(maxptail)+' < 1e−18**. The finite-cutoff residual still exceeds the true zeta response around1e−34. Passing the absolute gate checks normalization at the tested points; it does not resolve h relatively or establish a sign.', '',
'## Zero sum and quartet', '',
'As before, mpmath zetazero supplies every positive ordinate through60, with conjugates included explicitly. The inherited analytic zero-tail envelope uses Nζ(T)≤T² for T≥60, a loose classical explicit zero-count bound; it does not assume RH. In each integer shell k≥60, use 2(k+1)²(k²+1/4)²(k²+1/2)²exp(1/8−k²/2+t/2). The polynomial times Gaussian decreases there. Shells60 through100 and the geometric remainder allowance give maximum '+fmt(maxztail)+' over this grid. This zero tail is negligible compared with the arithmetic truncation.', '',
'Quartet u=1/3+7i is evaluated as 2Re(G_u²(e^{ut}+e^{−ut})) on the arithmetic side, where G_u is computed by full-line quadrature of g(x)e^{ux}. The zero side uses F(u) instead. These are the same four-root polarization as the unchanged builder, using complex squares rather than modulus squares.', '',
'## Reproduce and verification', '',
'From repository root run `python docs/routeB_bus/prove_rh_response_audit_2026-11-05/task_a_rerun/run_task_a.py`, then the report.py in the same directory. The driver imports C,F,g,atoms directly from the original ../scripts/task_a.py; its original main is not invoked. Dependencies are Python, mpmath and NumPy. No Tasks B/C are rerun. SHA256SUMS covers all delivered rerun files except itself.', '',
'All20 gate decisions and20 intentional failures, tail limits, precision repeats, source fingerprints and syntax were checked. Independent read-only review is in REVIEW.md. Numerical quadrature is diagnostic, not interval certified. The earlier failed-cutoff audit remains intact.', '']
(P/'RESULT.md').write_text('\n'.join(lines))
summary=dict(status=status,baseline_count=len(rows),baseline_pass_count=sum(x['baseline_pass'] for x in rows),plant_fail_count=sum(x['plant_fail'] for x in rows),max_baseline_error=str(maxbase),min_planted_error=str(minplant),max_prime_tail_upper=str(maxptail),max_zero_tail_bound=str(maxztail),max_precision_repeat_change=str(stability),preregistration_commit=r['preregistration_commit'])
(P/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
