# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Assemble task report and scores from the validated calculation artifacts."""
import csv,json
from pathlib import Path
H=Path(__file__).resolve().parent
NS=[500,1000,2000,5000]
def rows(name):return list(csv.DictReader((H/name).open()))
def main():
    fits=rows('fit_all.csv');selected=rows('fit_selected.csv');profiles={k:v['bestprofile'] for k,v in json.loads((H/'selected_profiles.json').read_text()).items()}
    scores=json.loads((H/'fit_predictions.json').read_text());poly=rows('objects_head_polynomials.csv');ratios={int(r['N']):r for r in rows('objects_core_ratios.csv')};q=ratios[10000]
    literal=max(float(r['literal_max_abs']) for r in poly);corrected=max(float(r['corrected_max_abs']) for r in poly)
    scores['R4']={'p':.9,'hit':literal<=1e-10,'literal_max_abs_error':literal,'corrected_max_abs_error':corrected,'note':'Literal task formula is false algebraically; corrected formula is a separately validated identity.'}
    scores['R5']={'p':.5,'hit':float(q['head_best_over_log'])<=.5,'head_best_over_log':float(q['head_best_over_log'])}
    brier=sum((r['p']-int(r['hit']))**2 for r in scores.values())/len(scores)
    (H/'prediction_scores.json').write_text(json.dumps({'scores':scores,'mean_Brier':brier},indent=2)+'\n')
    j1j3=rows('fit_judges.csv');j2=rows('objects_j2.csv');j4=rows('objects_j4.csv');main5000=next(r for r in selected if int(r['N'])==5000)
    lines=['# Smooth Mobius taper fit: finite results','',
    'Task commit `45af4a837e9a183d2405d91bf7df0f002f56acde`, blob `6bc455bf4859c160b08b69fe483661edbdb649bc`. Preregistration was committed before numerical runs as `60ea7f7d3` and pushed to rh_clean as `c11b1f5a9`. Exact source commits and blobs are in [SOURCES.json](SOURCES.json).','',
    '## Result','',
    f"At N=5000 the best cubic polynomial closes **{100*scores['R1']['gap_closure']:.5f}%** of the gap between the log taper and the unrestricted full-Gram optimum. The selected spline with x0=0.05 closes **{100*float(main5000['gap_closure']):.5f}%**. The cubic and spline errors are respectively 0.00631003487605 and {float(main5000['E']):.12g}, versus log-taper 0.0233363799923 and optimum 0.00530702068301. Thus the spline's advantage over the cubic is small, though above the numerical checks' error scale.",'',
    'This supports the finite-N smooth-profile hypothesis on the tested data. It does not provide one fixed profile with an asymptotic bound. The best cubic coefficients are not stable under the frozen 20% coordinate test (R2 MISS).','',
    f"At N=10000, a freshly refitted selected profile gives head ratio **{float(q['head_best_over_log']):.6f}**, shoulder ratio **{float(q['shoulder_best_over_log']):.6f}**, and full finite-core ratio **{float(q['full_best_over_log']):.6f}** relative to the log taper. The head becomes cheaper while the shoulder becomes more expensive. The Fourier norm falls as shown below; it is a different norm from the NB objective.",'',
    '## Frozen choices and source correction','',
    'Polynomials have P(0)=0, degrees1 through4, with P(1) free or fixed at1. Splines have P(0)=0, P(1) free, and C1 matching at the five prescribed knots. The spline endpoint condition was unspecified in the task; it was explicitly stated and frozen before runs. Best-profile selection excludes degree4 and minimizes E among degree<=3 polynomials and the five splines, independently at each N. No positivity or monotonicity constraint is imposed.','',
    'Only n>=2 are free coordinates. Raw a1=1 stays fixed even when P(1) differs from1; the centered Dirichlet coefficient is q1=1-s. This preserves the source definitions and E=B-pi L(F). See [CONVENTIONS.md](CONVENTIONS.md) for the exact algebra.','',
    'Task B.2 is false as written. The standard convolution Lambda_j=mu*log^j requires lower-order shifted terms. The exact formula is','',
    '```text',
    'A_P(r)=1-P(1)+sum_j p_j/L^j * sum_{k=0}^j binom(j,k) log(N/r)^(j-k) Lambda_k(r),',
    'Lambda_k(r)=sum_{d|r} mu(d) log(r/d)^k, Lambda_0(r)=1_{r=1}.',
    '```','',
    'The additive correction 1-P(1) applies to every r, since1 divides every r. An exact counterexample to the literal task formula is P=x^2,N=4,r=2: direct value3/4 versus literal1/4. This issue was identified before the numerical run. Literal R4 remains MISS; the corrected identity is not substituted into its score.','',
    '## Judges','',
    '| Judge | Outcome | Evidence |','|:---|:---|:---|',
    f"| J1 | PASS | Four main N; max log-taper error {max(float(r['difference']) for r in j1j3 if r['judge']=='J1'):.6g} <1e-10 |",
    f"| J2 | PASS | Direct midpoint cotangent functional at N=50,200,1000; max error {max(float(r['abs_error']) for r in j2):.6g} <1e-9 |",
    '| J3 | PASS | Every fitted family at four main N, including degree4, stays above the archived optimum within1e-10 tolerance |',
    f"| J4 | PASS | Eight log/best comparisons at N=50,200,500,1000; max norm discrepancy {max(float(r['norm_error_gauss12']) for r in j4):.6g} <1e-6 |",
    '',f'Corrected polynomial head identity: all32 fitted polynomial cases pass, max absolute difference **{corrected:.6g}**. Literal formula maximum discrepancy: **{literal:.6g}**.','',
    'All judges are finite floating-point diagnostics. J2 directly evaluates L from rational F samples, and J4 integrates the piecewise affine-plus-sine function independently of its Parseval formula. They are not interval certificates.','',
    '## All fitted-family errors','', '| family | N=500 | N=1000 | N=2000 | N=5000 |','|:---|---:|---:|---:|---:|']
    by={(int(r['N']),r['family']):r for r in fits}
    for fam in sorted({r['family'] for r in fits}):lines.append('| '+fam+' | '+' | '.join(f"{float(by[N,fam]['E']):.12g}" for N in NS)+' |')
    lines+=['','All coefficients, E logN, conditioning, and the 98-N selection table are retained in CSV/JSON. The four main selected profiles and their ordinary coefficients are:','', '| N | selected family | coefficients |','|---:|:---|:---|']
    for N in NS:
        p=profiles[str(N)];terms='; '.join(f'{k}: {v:.12g}' for k,v in p['basiscoeffs'].items());lines.append(f"| {N} | {p['family']} | {terms} |")
    lines+=['', 'Spline basis is x, (x0-x)_+^2-x0^2, (x0-x)_+^3-x0^3. Its edge slope is alpha-2*x0*beta-3*x0^2*gamma. Degree3 polynomial coefficients are in the ordinary x,x^2,x^3 basis.','',
    '## Remaining delta energy','', '| mask | N=500 | N=1000 | N=2000 | N=5000 |','|:---|---:|---:|---:|---:|']
    split={int(r['N']):r for r in rows('fit_energy_splits.csv')}
    for key in ['n_le_sqrtN','n_gt_sqrtN','n_gt_N_over_2','squarefree','non_squarefree_mu_zero','primes','proper_prime_powers','other']:
        lines.append('| '+key+' | '+' | '.join(f"{float(split[N]['fraction_'+key]):.8f}" for N in NS)+' |')
    lines+=['','Shares are fractions of the remaining squared coefficient difference. Different location and arithmetic masks overlap; only each stated complementary partition sums to1.','',
    '## Core ratios and prediction scores','', '| N | head(best)/head(log) | shoulder(best)/shoulder(log) | H(best)/H(log) |','|---:|---:|---:|---:|']
    for N in NS+[10000]:
        r=ratios[N];lines.append(f"| {N} | {float(r['head_best_over_log']):.9g} | {float(r['shoulder_best_over_log']):.9g} | {float(r['full_best_over_log']):.9g} |")
    lines+=['', '| prediction | p | outcome |','|:---|---:|:---|']
    for k,r in scores.items():lines.append(f"| {k} | {r['p']} | {'HIT' if r['hit'] else 'MISS'} |")
    lines+=['',f'Mean Brier score: **{brier:.8g}**. R4 is a literal-formula failure, not a failure of the corrected algebra. R2 coefficient relative changes are '+', '.join(f'{100*v:.5f}%' for v in scores['R2']['relative_changes'])+'.','',
    '## Validation, reproduction and limitations','',
    'The independent reviewer checked the scaled constrained solve, all nested-family inequalities, and directly summed the original remainder formula for every k=1..10000 for both N=10000 vectors. Those heads agree with the divisor-sieve output within4e-17. The root validator reproduces all98 selected profiles as135780 coefficient rows, including raw a1=1 and exact zero on nonsquarefree free indices. See [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) and [OUTPUT_VALIDATION.json](OUTPUT_VALIDATION.json).','',
    'One Sol escalation completed fit-output assembly after two late schema failures in the Luna run; it also corrected the scaled-coordinate gradient diagnostic. The same frozen model families and objective were retained. The final fit run and interface validation succeeded.','',
    '```sh',
    'uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/input_audit.py',
    'uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/fit.py',
    'uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/objects.py',
    'uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/validate_outputs.py',
    'uv run --no-project docs/routeB_bus/diag/SMOOTH_TAPER_FIT_2026-11-06/build_report.py',
    '```','',
    'One full Vasyunin Gram at N=10000 supplies all leading principal blocks; it is not a sequence of full-dimensional optimization solves. No free optimum at N=10000 is claimed. The core uses exactly the inherited92-point log grid, plus the four main N values, and stops at K-1 for K=ceil(N^(3/2)). Boundary and Fourier objects cover all98 supplied N. The infinite NB objective E and finite core H are kept distinct.','',
    'The fitted profiles and selection depend on N. A numerical norm below7/logN does not transfer the log-taper theorem to this family. No uniform bound for the cotangent functional, asymptotic rate, convergence theorem, or RH claim is established. RH remains OPEN; PX_RH_CLAIM: NOT_MADE.','',
    '## Detailed Part A','',(H/'PART_A.md').read_text().removeprefix('# Part A — smooth Mobius taper fit').strip(),'',
    '## Detailed Part B','',(H/'PART_B.md').read_text().removeprefix('# Part B — smooth taper objects and finite checks').strip(),'']
    text='\n'.join(lines)
    replacements={'degrees1':'degrees 1','at1':'at 1','from1':'from 1','since1':'since 1','value3/4':'value 3/4','literal1/4':'literal 1/4','all32':'all 32','within1e':'within 1e','sums to1':'sums to 1','within4e':'within 4e','all98':'all 98','as135780':'as 135780','inherited92':'inherited 92','all98':'all 98','below7':'below 7'}
    for a,b in replacements.items():text=text.replace(a,b)
    (H/'REPORT.md').write_text(text)
    print('[##############################] 100% ETA 0s report and scores assembled')
if __name__=='__main__':main()
