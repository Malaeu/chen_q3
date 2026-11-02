"""Build human-readable ledgers and validate saved identities, no eigenproblems."""
from pathlib import Path
import csv,json,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=160
M=lambda x:mp.mpf(x)
fmt=lambda x:mp.nstr(M(x),10)
matched=list(csv.DictReader((P/'matched.csv').open()))
ledgers=[json.loads(x.read_text()) for x in sorted((P/'ledger_cells').glob('*.json'))]
assert len(ledgers)==12 and len(matched)==15
codehash=hashlib.sha256((P/'ledger.py').read_bytes()).hexdigest()
checks={};groups=[]
for d in ledgers:
 s=d['summary'];case=Path(d['source_file']).stem
 assert hashlib.sha256((P/d['source_file']).read_bytes()).hexdigest()==d['source_sha256']
 assert codehash==d['code_sha256']
 assert all(M(x['raw_P'])==0 for x in d['atoms'] if x['endpoint_atom'])
 for key in ['direct_ledger_minus_Rayleigh','Abel_closure_error','derivative_identity_coefficient_error','independent_correlation_error','reference_Abel_closure_error']:
  if s.get(key) is not None:checks[key]=max(checks.get(key,M(0)),abs(M(s[key])))
 assert abs(M(s['vector_norm_squared'])-1)<M('1e-120')
 for key,sign in [('H_original','positive'),('constant_original','negative'),('pole','positive' if s['world']=='zeta' else 'absent')]:
  groups.append(dict(case=case,world=s['world'],m=s['m'],q=s['q'],cutoff_mode=s['cutoff_mode'],component=key,coefficient_sign=sign,raw_arithmetic_P='',signed_form_contribution=s[key]))
 for key,value in d['groups'].items():
  sector,sign=key.split('_b_');groups.append(dict(case=case,world=s['world'],m=s['m'],q=s['q'],cutoff_mode=s['cutoff_mode'],component=sector,coefficient_sign=sign,raw_arithmetic_P=value['raw_P'],signed_form_contribution=value['signed_ledger_minus_P']))
 assert abs(sum(M(x['signed_form_contribution']) for x in groups if x['case']==case)-M(s['same_vector_Rayleigh']))<M('1e-117')
assert checks['direct_ledger_minus_Rayleigh']<M('2e-118')
assert checks['Abel_closure_error']<M('2e-137')
with (P/'ledger_groups.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(groups[0]));w.writeheader();w.writerows(groups)
(P/'VALIDATION.json').write_text(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','matched_cells':len(matched),'ledger_cells':len(ledgers),'groups':len(groups),'maximum_absolute_errors':{k:mp.nstr(v,40) for k,v in checks.items()},'checks':['unit physical vector','source and implementation hashes','all endpoint atoms exactly zero','sum of signed groups equals same-vector Rayleigh','independent physical correlation and moving-boundary derivative identity','segmented Abel closure'],'interval_certificate':False},indent=2)+'\n')
s='''# Equal-density and signed-ledger comparison: zeta versus DH

DIAGNOSTIC_NEVER_A_PROOF

Base: rh_clean `d26831357b6cb3b2b7d4a569d2031e454952b246`. The pinned kernel source is `c31645a3efd410417f6e2027b4474711bd443348`, blob `98380adf97aab19a900e332b6583c8f731b6d3f6`; its exact bytes are retained in SOURCE_KERNEL_PINNED.md and verified in source_pin.json.

## A. Equal constraint density

For zeta the baseline is T=1.1*(2pi m/log m). DH T is the midpoint between consecutive distinct zero heights giving the same real constraint count q. Each off-line reflected pair supplies two real constraints. Rank=q and dim J=m+1-q in these cells. No row scaling is used for the reported singular values. Delta is the full operator norm ||A Q||, not just the compressed form norm. The count includes all levels below delta*(1+1e-6).

At m=120 the requested exact match is impossible: zeta has q=64, while the DH count jumps from63 to65 at the reflected pair of height114.163342730757. Splitting that pair would change the quiet-space definition. Both DH neighbors are retained. Additional zeta q63/q65 cells give exact same-cardinality bracket comparisons; they are explicitly additional to the zeta kappa1.1 baseline q64.

|m|world|q=rank|dim J|T|delta|sigma_min(F)|N(delta+)-dim J|
|---:|---|---:|---:|---:|---:|---:|---:|
'''
for r in sorted((x for x in matched if int(x['m'])!=55),key=lambda x:(int(x['m']),int(x['q']),x['world'])):
 s+=f"|{r['m']}|{r['world']}|{r['q']}|{r['dim_J']}|{fmt(r['T'])}|{fmt(r['delta'])}|{fmt(r['sigma_min'])}|{r['count_minus_dim']}|\n"
s+='''
The equal-density DH kernels are not quiet: residuals are roughly6–11, while their raw capacities remain of order0.4–0.8. Thus the previous small DH residuals at the same kappa were not preserved by equalizing the number of constraints. This finite comparison does not establish an asymptotic rate or a uniform zeta bound. At the chosen zeta baseline only m20 saturates its own residual count among these exact baseline cells; the other finite count excesses remain explicit.

## B. Signed form on the complement minimum

All components are evaluated on the **same unit vector f** within each case: f minimizes U^T A U and is lifted by orthonormal U. This is the complement bottom, not necessarily the full-carrier bottom. Different worlds/cutoffs have different minimizing vectors, so subtracting their entries is descriptive rather than a common-vector operator comparison.

Because B did not separately specify its cutoff, both density-matched complements and native kappa1.1 complements are included. At m120 the extra zeta bracket complements are included as well:12 ledgers total. The native comparison is shown first below. Every arithmetic entry is the signed form contribution **minus P**; plus/minus labels refer to the sign of b(n), not the sign of the evaluated summand. Scalar H has positive kernel coefficient, c is the signed negative constant, and the pole coefficient is positive for zeta and absent for DH. Empty bins are exact zeros.

The original ledger is lambda=H_original+c+pole−sum P. It uses j_zeta=exp(−s/2)/(1−exp(−2s)), c_zeta=−gamma−log(8pi)−pi/2; DH uses j_D=exp(−3s/2)/(1−exp(−2s)), c_D=−gamma−log(8pi/5)+pi/2, and no pole.

|signed component|zeta55|DH55 native|zeta80|DH80 native|zeta120|DH120 native|
|---|---:|---:|---:|---:|---:|---:|
'''
lookup={Path(d['source_file']).stem:d['summary'] for d in ledgers}
native=[lookup[x] for x in ['zeta_m55_q27','dh_m55_q50_native','zeta_m80_q41','dh_m80_q73_native','zeta_m120_q64','dh_m120_q108_native']]
keys=[('H_original','H_original'),('c','constant_original'),('pole','pole')]+[(sector+'; b '+sign,'signed_minus_P_'+sector+'_b_'+sign) for sector in ['prime','square','higherpower','nonprimepower'] for sign in ['positive','negative']]+[('sum = complement lambda','same_vector_Rayleigh')]
for title,key in keys:s+='|'+title+'|'+'|'.join(fmt(r[key]) for r in native)+'|\n'
s+='''
The full signed split for all12 cases is in ledger_groups.csv; per-atom values, coefficient signs, endpoint zeros and vectors are in ledger_cells/. At native DH m120 the non-prime-power contribution alone is about−4.56181355 on that selected vector (both coefficient signs contribute negatively). This is a same-vector ledger observation, not the minimum eigenvalue of a matrix with those atoms removed.

## Boundary, interior and compensation

The pinned Markdown actually numbers the relevant formulas (2.2), (2.4)–(2.5), (3.3)–(3.4), and (6.1); it has no displayed equation(12). SOURCE_CONVENTIONS.md gives precise source line anchors. To avoid silently assigning a meaning to the different labels in the request, the following definitions are explicit:

- B=2 f(L/2) integral a(s) f(L/2−s) ds.
- I=T_half+Bulk, with T_half=integral a(s)Q(s)/2 ds and Bulk=−2 integral a(s) integral f(x)f'_int(x+s) dx ds.
- All three pieces are saved separately; the Q/2 term is never omitted.

For zeta a=exp(−s/2)[psi(exp s)−(exp s−1)], so P−I_L=B+I, with I_L=integral exp(s/2)Q(s)ds. The compensated zeta identity is lambda=H_plus+(4−cstar)−B−I, where H_plus uses exp(−5s/2)/(1−exp(−2s)). H_original, c_original and the pole must not be mixed with that compensated formula.

For DH the canonical arithmetic Abel split uses a_D=exp(−s/2)Psi_D(exp s), giving P_D=B_D+I_D and lambda=H_D+c_D−B_D−I_D. We additionally evaluate the same x−1 reference subtraction as zeta for comparability: P_D−I_L=B_ref+I_ref and lambda=H_D+c_D−I_L−B_ref−I_ref. This additional reference is **ARBITRARY_REFERENCE_NO_POLE_CANCELLATION**; it does not manufacture a DH pole or main term.

Native kappa1.1 comparison using the common x−1 reference:

|world|m|B_ref|T_half_ref|Bulk_ref|I_ref=T_half+Bulk|I_L|
|---|---:|---:|---:|---:|---:|---:|
'''
for r in native:
 vals=[r[k] for k in ['reference_B','reference_T','reference_derivative_bulk','reference_full_interior','continuum_I_L']]
 s+=f"|{r['world']}|{r['m']}|"+'|'.join(fmt(x) for x in vals)+'|\n'
s+='''
The canonical raw-DH boundary/interior are also retained, separately labeled. Boundary signs and magnitudes depend on the selected vector and the reference subtraction. These data do not justify deleting the interior derivative term or attributing the entire sign change to the boundary.

## All selected complement bottoms

|world|m|q|cutoff mode|complement minimum|
|---|---:|---:|---|---:|
'''
for d in sorted(ledgers,key=lambda d:(d['summary']['m'],d['summary']['world'],d['summary']['q'])):
 r=d['summary'];s+=f"|{r['world']}|{r['m']}|{r['q']}|{r['cutoff_mode']}|{fmt(r['same_vector_Rayleigh'])}|\n"
s+='''
In particular, matched DH55/80 complements remain positive (+0.54875544,+0.65436037), while their native kappa1.1 complements are negative. Both matched DH120 branches are negative. Cutoff selection is therefore part of the reported result, not a hidden normalization choice.

## Validation and reproduction

Matrices/spaces use120dps; the ledger evaluation uses140dps and an independent160-point,8-panel archimedean quadrature. The fast zeta builder agrees with saved180dps m20 entries within2.90e-119 (Frobenius6.90e-119). Physical exponential-product correlations independently check the modal q_even contraction and the moving-boundary derivative identity. Abel integrals use exact exponential moments separately on every[log n,log(n+1)], including signed DH non-prime-power coefficients. All n=m atoms are retained with exactly zero correlation weight.

'''
s+='Maximum absolute closure errors:\n\n'+''.join('- '+k+': '+mp.nstr(v,7)+'\n' for k,v in checks.items())
s+='''
These are multiprecision agreement checks, not outward-rounded interval certificates. The DH zero census and80-digit nodes retain the qualifications of the parent fake-world dataset. No cofinal bound, new RH sign, or route promotion is claimed.

Run `python3 unpack_cells.py` to verify and restore the raw matched_cells/ directory from the split lossless archive. MATCHED_ARCHIVE.json records every source/cell SHA-256. matched.py reproduces matrix/space cells; ledger.py produces the signed and Abel ledgers; summarize_ledger.py validates saved identities and recreates this report. density_plan.py independently checks the exact-count cutoff plan. SHA256SUMS covers the committed package.
'''
(P/'RESULT.md').write_text(s)
print(json.dumps({'checks':{k:mp.nstr(v,7) for k,v in checks.items()},'groups':len(groups)}))
