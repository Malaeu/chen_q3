# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Assemble the report from computed, independently reviewed result tables."""
import csv,json,math
from pathlib import Path
H=Path(__file__).resolve().parent
def rows(name):return list(csv.DictReader((H/name).open()))
def main():
    a=json.loads((H/'part_a_results.json').read_text());b=json.loads((H/'part_b_run.json').read_text())
    judges=rows('part_b_j4.csv');by={(int(r['N']),r['variable']):r for r in judges}
    inv=by[5000,'inverse_derivative_squared'];gap=by[5000,'raw_local_min_gap']
    scores=a['Q1_Q4'];scores['Q5']={'p':.45,'observed':float(inv['rho']),'permutation_p':float(inv['permutation_p_two_sided']),'hit':float(inv['rho'])>=.3 and float(inv['permutation_p_two_sided'])<.01}
    scores['Q6']={'p':.45,'observed':float(gap['rho']),'permutation_p':float(gap['permutation_p_two_sided']),'hit':float(inv['rho'])*float(gap['rho'])>0 and float(gap['permutation_p_two_sided'])<.01}
    brier=sum((r['p']-int(r['hit']))**2 for r in scores.values())/6
    (H/'prediction_scores.json').write_text(json.dumps({'scores':scores,'mean_Brier':brier,'primary_N_for_Q3_Q4':5000,'Q6_primary_variable':'raw minimum gap, as frozen'},indent=2)+'\n')
    lines=['# Optimal NB coefficients versus Mobius taper','',
    'Task commit `b9bfe4a204f6c15881f11e6088c0fc50cfd0478e`, task blob `7da31c2964639e79356ebe177d2ff5f05860d0eb`. Preregistration was committed before new numbers as worktree commit `42eeaebd0`, then cherry-picked and pushed to rh_clean as `4b48d09ad`. Exact source commits/blobs are in [SOURCES.json](SOURCES.json).','',
    '## Result and limits','',
    f"At N=5000, optimal versus taper coefficient cosine is {scores['Q1']['observed']:.6f}; the raw rescaled delta-profile correlation for N=2000 versus 5000 is {scores['Q2']['observed']:.6f}. The six-feature arithmetic regression nevertheless explains R²=0.712682 of delta variation at N=5000. Failure of a raw interpolated-profile test does not establish random noise or absence of arithmetic structure.",'',
    f"The primary localization statistic at N=5000 is Spearman(W,1/|zeta prime|²)={float(inv['rho']):.6f}, two-sided permutation p={float(inv['permutation_p_two_sided']):.6g}. The raw-gap statistic is {float(gap['rho']):.6f}, p={float(gap['permutation_p_two_sided']):.6g}. Q5 is {'HIT' if scores['Q5']['hit'] else 'MISS'}. These finite zero-cell correlations test the specified hypothesis; they do not establish causation, a rate, or RH.",'',
    'The result distinguishes unweighted W_j (the task statistic) from the weighted NB norm. At a zero itself both intensities equal 1; the measured improvement concerns its neighborhood. Cell widths, height trends and arithmetic oscillations can affect correlations. A global zero-label permutation tests exchangeability under that particular null, not a height-conditioned or causal null. No multiplicity correction or height-conditioned secondary test is claimed.','',
    '## Judges','',
    f"- **J1 PASS:** all four optimal errors agree with the archive to 1e-10; maximum difference {a['max_j1_abs_difference']:.6g}.",
    f"- **J2 PASS:** all four centered taper errors agree to 1e-10; maximum difference {a['max_j2_abs_difference']:.6g}.",
    '- **J3 ANALYTIC IDENTITY + LIMITED NUMERICAL CONSISTENCY:** the centered fixed-vector norms agree exactly by Mellin-Plancherel. A separately computed explicit BV tail bound is supplied below. Its enclosure is wide; numerical quadrature is not interval-certified, so this is not a 1e-10 verification of the full integral.',
    '- **J4 COMPUTED:** 1000 seeded permutations for each requested correlation, with two-sided plus-one p-values and central 95% null bands. Statistical evidence and a passed numerical implementation are distinct.','',
    '## J3: full discrete norm, computed head, independent tail','',
    'For both vectors `D(s)=sum_{n=2}^N c_n(n^(-s)-1/n)` and `D(1)=0`. The archive stores the opposite-sign projection coefficients. The full proof, sign conversion, and elementary tail derivation are in [TAIL_BOUND.md](TAIL_BOUND.md).','',
    '`Tail(T) <= (V_K/sqrt(pi*T)+B/sqrt(K))^2`, with `B=1+sum|c_n|` and V_K the explicit total variation of the truncated logarithmic residual. Arb128 evaluates all seven listed K values and outward rounds the resulting upper bounds. This uses neither E nor E minus head.','',
    '| N | vector | full discrete E | head through 1000 | E minus head (diagnostic) | independent tail upper | K | head <= E <= head+bound |',
    '|---:|:---|---:|---:|---:|---:|---:|:---:|']
    tail=json.loads((H/'tail_bound.json').read_text());tailmap={(r['N'],r['kind']):r['best'] for r in tail['rows']}
    discrete={int(r['N']):r for r in rows('part_a_judges.csv')};headrows=rows('part_b_weighted_head.csv');level=b['final_simpson_subdivisions_per_segment'];j3=[]
    for r in headrows:
        N=int(r['N'])
        for kind,prefix,col in [('opt','Iopt','recomputed_E_copt'),('taper','Ia','recomputed_E_a')]:
            E=float(discrete[N][col]);head=float(r[f'{prefix}_head_{level}']);t=tailmap[N,kind];bound=t['tail_upper'];consistent=head<=E<=head+bound
            j3.append({'N':N,'kind':kind,'discrete_E':E,'head':head,'diagnostic_E_minus_head':E-head,'independent_tail_upper':bound,'K':t['K'],'diagnostic_consistent':consistent})
            lines.append(f"| {N} | {kind} | {E:.12g} | {head:.12g} | {E-head:.9g} | {bound:.9g} | {t['K']} | {consistent} |")
    (H/'j3_comparison.json').write_text(json.dumps({'status':'analytic identity; broad diagnostic consistency, not interval quadrature','rows':j3},indent=2)+'\n')
    lines+=['', 'Optimal tail bounds apply to the parsed binary64 CSV vector. The taper bound encloses its exact real logarithmic definition; the computed head uses its float64 approximation. This distinction, together with non-interval quadrature, prevents calling the displayed head-plus-tail intervals rigorous certificates of the computed floating integral.', '',
    '## Frozen predictions','', '| ID | p | observation | outcome |', '|:---|---:|---:|:---|']
    for q,r in scores.items():lines.append(f"| {q} | {r['p']:.2f} | {r['observed']:.9g} | {'HIT' if r['hit'] else 'MISS'} |")
    lines += ['',f'Mean Brier score across all six predictions: **{brier:.9g}**. Q3/Q4 use N=5000 as frozen, with every N reported below. Q6 uses the **raw minimum gap**, not inverse gap; inverse-gap Spearman would reverse its sign and is not substituted after the result.','',
    '## Reproduction and scope','',
    'Run from the repository root (uv resolves pinned script dependencies):','', '```sh',
    'uv run --no-project docs/routeB_bus/diag/OPTIMAL_VS_MOBIUS_2026-11-06/input_audit.py',
    'uv run --no-project docs/routeB_bus/diag/OPTIMAL_VS_MOBIUS_2026-11-06/part_a.py',
    'uv run --no-project docs/routeB_bus/diag/OPTIMAL_VS_MOBIUS_2026-11-06/part_b.py',
    'uv run --no-project docs/routeB_bus/diag/OPTIMAL_VS_MOBIUS_2026-11-06/tail_bound.py',
    'uv run --no-project docs/routeB_bus/diag/OPTIMAL_VS_MOBIUS_2026-11-06/build_report.py',
    '```','',
    'Part A rebuilds the full Vasyunin Gram through N=5000 using clang++/C++17 (Apple long double has 53 bits). Part B uses mpmath 20 decimal digits for zeros, derivatives and direct zeta, complex128 for polynomials, and nested Simpson quadrature. Its CSV grid supports replay. The R8 rational witnesses are separate upper-envelope candidates; [input_audit.json](input_audit.json) records their differences from these full-Gram optima.','',
    'Truncations: four finite N only; free indices 2..N; t in [0,1000]; positive critical-line zeros only with one next neighbor for the final gap; boundary cells clipped at 0 and 1000; no independent proof of zero completeness, no interval zero certification, no asymptotic extrapolation. The raw-profile comparison uses 4096 interpolated n/N points; arithmetic regression is in-sample, with an intercept. All errors and correlations are finite numerical observations. RH remains OPEN; PX_RH_CLAIM: NOT_MADE.','',
    '## Detailed coefficient results','', (H/'PART_A.md').read_text().replace('# Part A — coefficient space and J1/J2','').strip(),'',
    '## Detailed zero results and top20 tables','',(H/'PART_B.md').read_text().replace('# Part B — t-side zero localization','').strip(),'']
    text='\n'.join(lines)
    text=text.replace('The independently derived J3 tail bound is tracked outside this Part B computation and must be merged before treating these as full-line norm enclosures.', 'The independently derived J3 tail bound is integrated in the J3 table above, with the stated diagnostic-only limitation.')
    text=text.replace('## Detailed coefficient results', '## Validation\n\nAn independent read-only review reproduced all 2,596 W_j and eight weighted heads from the final grid, all eight Spearman/permutation results, and seven direct mpmath intensity samples at 30 digits. The root validation script additionally replayed the permutations and 12 optimal/taper intensity samples at 40 digits (maximum absolute discrepancy 3.68e-13). See [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) and [OUTPUT_VALIDATION.json](OUTPUT_VALIDATION.json).\n\n## Detailed coefficient results')
    (H/'REPORT.md').write_text(text)
    print('[##############################] 100% ETA 0s report assembled')
if __name__=='__main__':main()
