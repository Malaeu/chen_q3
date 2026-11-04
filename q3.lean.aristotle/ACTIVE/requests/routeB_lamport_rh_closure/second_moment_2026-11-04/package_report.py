"""Assemble finite diagnostic report and input receipts from completed measurements."""
from pathlib import Path
import csv,json,hashlib,subprocess
P=Path(__file__).resolve().parent
R=Path('/workspace/stiffness/repo')
def rows(n):return list(csv.DictReader((P/n).open()))
s=rows('SUMMARY.csv');d=rows('DECOMPOSITION.csv');sc=json.loads((P/'SCORES.json').read_text())
def primary(w,m=300):return next(r for r in s if r['world']==w and int(r['m'])==m and r['cutoff']=='primary' and r['sigma_convention']=='L_plus_inv_gamma')
report='''# Second moment of the literal even CCM window

Route B = CHALLENGER / NOT_RH. DIAGNOSTIC_NEVER_A_PROOF.

Completed all 855 world/window measurements, m=16,…,300, and 5,130 census/cutoff/σ combinations. The requested raw rank–trace scores fail SANITY. Interpretation of **all three σ conventions is stopped**, as required; measured moments and descriptive comparisons remain recorded. No route-state or RH export is made.

## Measured outcomes

With the registered primary cutoff and σ=L+1/γ*, ζ has v in [0.8455393,0.9093495] for m≥80. Its median on 200…300 is 0.8995755. These finite values do not imply a positive proportion or a cofinal bound. The σ=2L values are smaller still because the denominator was enlarged; the raw transfer formula is not invariant under this change.

| Registered prediction | Result |
|---|---|
| V1 (0.60): every ζ m≥80 in [1,1.6] | FAIL: all are below 1 |
| V2 (0.35): median ζ 200…300 <4/3 | PASS as a raw measured comparison only |
| V3 (0.70): arithmetic off-diagonal ≥20% at m300 | FAIL: 1.2119% signed net; 8.7171% even after summing absolute individual cross terms |
| V4 (0.85): census SANITY everywhere | FAIL; interpretation of all three σ conventions stopped |

| World, m300 | tr A | ‖A‖²F | N(T) | v, primary preferred σ | simple-on-line census fraction |
|---|---:|---:|---:|---:|---:|
'''
for w in ['zeta','dh','plant']:
 r=primary(w);report+=f"| {w} | {float(r['trace']):.9f} | {float(r['Frob2']):.9f} | {r['N_upper_with_multiplicity']} | {float(r['v']):.9f} | {float(r['census_simple_on_line_fraction']):.9f} |\n"
report+='''
## Why the finite count interpretation stops

The pinned 07a242c1 verdict explicitly concerns the **physical even block**. We retained that normalization, the m+1 cosine coordinates, its pole and source signs, and positive-height census multiplicities. We applied no compensating factor of two. An independent analytic source check agrees at m16 in all three worlds; all 855 primary census counts agree with the b785505e ground-state packet.

Equations (4.5)–(4.6) of the verdict use asymptotic trace closure with σ=L+O(1), a paid tail and an o(1) remainder. Omitting that remainder does not produce a finite inequality. The directly measured, **unpaid** finite trace expression is

Φ=(4 tr(A)/σ−‖A‖²F/σ²)/N,

with scores Φ−2 and (Φ−1)/2. It is included separately, without replacing the registered raw scores 2−v and (3−v)/2. In particular, if σ=aL and the leading trace scale is LN, the formal leading scores become 4/a−v−2 and (4/a−v−1)/2. For σ=2L these are −v and (1−v)/2, not the requested raw formulas. σ=L is an exploratory convention, not a guaranteed uniform sampling cap.

At ζ m300 primary, tr(A)/(σN)≈0.847888, rather than 1. Consequently raw 2−v≈1.101966 and (3−v)/2≈1.050983 exceed the census fraction 1. This is a normalization/finite-transfer flag, not a disproof of the conditional sampling cap. No change to N, no clipping to 1 and no reinterpretation rescues the registered scores.

For every primary cell the additional unpaid finite trace scores pass the census comparison. That check supplies neither a tail payment nor a finite count certificate. Some κ=1 unpaid scores also fail; κ=1 is outside the positive-c tail-payment theorem used in the verdict.

Counts below are cells with either raw score exceeding its corresponding census fraction; each entry has 285 cells. The tolerance is 1e−10·max(1,|raw simple|,|raw distinct|).

| World | cutoff | L+1/γ* | 2L | L |
|---|---|---:|---:|---:|
'''
a=rows('SANITY_SUMMARY.csv')
for w in ['zeta','dh','plant']:
 for cutoff in ['primary','kappa1']:
  counts=[next(r['violations'] for r in a if r['world']==w and r['cutoff']==cutoff and r['sigma_convention']==sig)for sig in ['L_plus_inv_gamma','2L','L']]
  report+=f"| {w} | {cutoff} | {' | '.join(counts)} |\n"
report+='''
N(T) counts positive-height zeros with multiplicity: one for a line zero, two for an off-line quartet. The simple fraction here means simple **on the line**. Distinct complex zeros are not distinct heights: the tabulated DH/plant pairs contain two distinct upper-half-plane points. All tabulated points are treated as simple according to the supplied census; this run supplies no new simplicity or census completeness theorem.

## Source decomposition

A=G+P+B+W. G is the archimedean constant, integral and tail; P is the even ζ pole (zero for DH); B retains every signed arithmetic atom. W is the pinned plant innovation, zero in ζ and DH. Thus the requested C=G+P, and the plant perturbation is separately accounted for. Off-diagonal means n≠k for individual integer atoms, including distinct powers of the same prime. DH keeps non-prime-power atoms and negative coefficients.

| Component, m300 | ζ | DH | plant |
|---|---:|---:|---:|
'''
for c in ['G2','P2','GP','GB','PB','B_diagonal','B_offdiagonal','W2','GW','PW','BW']:
 vs=[next(float(r['value'])for r in d if r['world']==w and r['m']=='300' and r['component']==c)for w in ['zeta','dh','plant']]
 report+=f"| {c} | "+' | '.join(f'{v:.6f}'for v in vs)+' |\n'
report+='''
Mixed terms already include factor 2. B_offdiagonal is signed; ARITHMETIC_PAIR_MASS_m300.csv additionally separates positive, negative and absolute individual cross contributions. All 855 Frobenius decompositions close with maximum relative residual 8.02e−15. The largest entrywise atom reconstruction residual is 1.27e−12; C+B+W reconstruction is 4.11e−15. Endpoint atoms at n=m are exactly zero. Coefficient-count metadata reflects the unchanged numerical recurrence, including negligible exact-zero ghosts; it is not an exact arithmetic support census.

## Finite trend and reference family

Primary preferred-σ ζ medians are 0.872794 (100–149), 0.886085 (150–199), 0.895214 (200–249), 0.902448 (250–299); m300 alone is 0.898034. BLOCK_MEDIANS.csv contains every world, cutoff and σ, with sample sizes. FINITE_FITS.csv describes v=a+b/log m only within 80…300. No fitted coefficient is asserted to be a limiting value.

SUMMARY.csv reports λ_eff=L/(L−log L+log κ) in every row and the reference 1/λ_eff+λ_eff/3. The Gabor-family reference is not an identity for this literal CCM block. This run neither identifies the two Gram matrices nor transfers a constant between them.

## Sharper conditional σ

For ζ only we also evaluate the uniform scalar envelope σ_sharp=L+sup_{γ≥γ*} sin(Lγ)/γ, using the diagnostic first ordinate γ*. Its maximum is at the boundary or the next positive stationary peak of sinc, whose heights subsequently decrease. This improves L+1/γ* by about 6.34e−6…0.00854 over this grid. See sigma_sharp.md and SHARP_SIGMA_RESULTS.csv. This assumes γ* as the lower height bound; it is not a new zero-free proof and does not repair the finite transfer or the stopped interpretation.

## Precision, replay and artifacts

Unchanged pinned source builder: 400-bit MPFR, GL192, eight panels. Matrix moments and atom decomposition use binary64. Paired GL256 checks at m16,40,300 keep the same precision; MP A differences are at most 1.15e−115 and Frobenius differences at most 1.22e−112. These are sensitivity checks, not interval certificates. No eigensystem, new spectral scan, precision escalation or cofinal extrapolation is used.

SOURCE_MOMENTS.csv records hashes of all regenerated local A/C/B arrays and NPZ files. Dense arrays remain local. INPUTS.json pins source files and the complete inbox verdict copied as INPUT_VERDICT.md. REPRODUCE.md gives the replay order; verify.py checks the committed scalar packet and SHA256SUMS. Canon and mirror contain identical blobs in one commit.
'''
# Use calculated block medians instead of approximate hand transcription.
b=rows('BLOCK_MEDIANS.csv');v=next(float(r['median_v'])for r in b if r['world']=='zeta'and r['cutoff']=='primary'and r['sigma_convention']=='L_plus_inv_gamma'and r['m_start']=='100');report=report.replace('0.872794 (100–149)',f'{v:.6f} (100–149)')
(P/'RESULT.md').write_text(report)
paths=['docs/routeB_bus/arithmetic_coupling_2026-11-03/source/split.py','docs/routeB_bus/arithmetic_coupling_2026-11-03/RESULT.md','docs/routeB_bus/arithmetic_coupling_2026-11-03/source_inputs/zeta_zeros.csv','docs/routeB_bus/arithmetic_coupling_2026-11-03/source_inputs/dh_zeros_900_200dps.json','docs/routeB_bus/ground_state_zeros_2026-11-03/RESULT.md','docs/routeB_bus/ground_state_zeros_2026-11-03/ZERO_SUMMARY.csv','docs/routeB_bus/ground_state_zeros_2026-11-03/inputs/analytic_source.py']
inputs=[]
for path in paths:
 data=(R/path).read_bytes();inputs.append(dict(path=path,git_blob=subprocess.check_output(['git','rev-parse','b785505e:'+path],cwd=R,text=True).strip(),sha256=hashlib.sha256(data).hexdigest()))
v=(P/'INPUT_VERDICT.md').read_bytes();inputs.append(dict(path='docs/routeB_bus/proshka/PROSHKA_VERDICT_ZERO_DENSITY_TAIL_Q3_DIAGNOSIS_2026-11-04.md',ref='07a242c1',git_blob='29647418b82ade2eca870a6d68592c1bf9c51859',sha256=hashlib.sha256(v).hexdigest()))
(P/'INPUTS.json').write_text(json.dumps(dict(base='b785505e569457b79b4887764b450559010c8b16',arithmetic_builder_origin='89e8c969',status='DIAGNOSTIC_NEVER_A_PROOF',inputs=inputs),indent=2)+'\n')
