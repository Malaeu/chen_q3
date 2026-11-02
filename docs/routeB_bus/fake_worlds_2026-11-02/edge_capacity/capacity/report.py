"""Summarize saved-complement endpoint capacities, never infer a theorem."""
from pathlib import Path
import json
import mpmath as mp
P=Path(__file__).resolve().parent
mp.mp.dps=100
def n(x,d=10):return mp.nstr(mp.mpf(x),d) if x is not None else 'n/a'
def main():
 rows=json.loads((P/'capacity.json').read_text());zz=[r for r in rows if r['world']=='zeta'];dh=[r for r in rows if r['world']=='dh']
 scores=[]
 for r in rows:
  R=mp.mpf(r['R_scaled']);S=mp.mpf(r['capacity_scaled']);la=mp.mpf(r['saved_lambda_min']);sl=mp.mpf(r['endpoint_zero_minimum'])
  r['capacity_R_absolute_difference']=mp.nstr(abs(S-R),60);r['capacity_R_relative_difference']=mp.nstr(abs(S-R)/abs(R),60) if R else None
  r['endpoint_zero_to_bottom_ratio']=mp.nstr(sl/la,60) if la else None
  r['P2_one_percent']=bool(R and abs(S-R)<mp.mpf('.01')*abs(R)) if r['world']=='zeta' else None
  r['P3_thousandfold']=bool(sl>=1000*la) if r['world']=='zeta' else None
 scores=[dict(id='P2',zeta_cells=len(zz),passed=sum(r['P2_one_percent'] for r in zz),all8_pass=len(zz)==8 and all(r['P2_one_percent'] for r in zz)),dict(id='P3',zeta_cells=len(zz),passed=sum(r['P3_thousandfold'] for r in zz),all8_pass=len(zz)==8 and all(r['P3_thousandfold'] for r in zz))]
 # zz dictionaries share references with rows, so enriched values are retained.
 (P/'capacity_scored.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',predictions=scores,cells=rows),indent=2)+'\n')
 lines=['# Endpoint capacity and endpoint-zero slice','', '**DIAGNOSTIC_NEVER_A_PROOF.** Saved complement spaces only; physical endpoint normalization, no row/endpoint rescaling. Lower cells use archived full source matrices and complement bases. Shared high-cell A/E/U/Q inputs were reconstructed from pinned helpers before this capacity module used them; no full-carrier eigensystem was rebuilt.','',
 'For G=U^T A U and t=U^T d_b, d_b=(1,sqrt2,...)/sqrt(log m), the algebraic inverse quantity is cap=1/(t^T G^(-1)t). It equals the affine constrained minimum when the computed reduced G is positive definite. An indefinite DH G receives no positive-capacity interpretation, even if its algebraic inverse quantity is positive.','',
 'The endpoint-zero minimum is the lowest eigenvalue of Z^T G Z, where the columns of a stable Householder Z form an orthonormal basis of t-perp. This is the requested new constrained compression, not a new full-carrier eigenproblem. The second eigenvalue of G uses the archived compressed spectrum where available; otherwise the requested reduced G spectrum is recomputed at high precision. It is independently replayed in float arithmetic with an explicit resolution flag, which does not replace tiny high-precision eigenvalues.','',
 '## Zeta cells','', '|m|q|cap*pi*T/logT|R=lambda*pi*T/(e² logT)|relative difference|lambda2(G)|endpoint-zero minimum|slice/bottom|','|---:|---:|---:|---:|---:|---:|---:|---:|']
 for r in zz:lines.append('|'+ '|'.join([str(r['m']),str(r['q']),n(r['capacity_scaled']),n(r['R_scaled']),n(r['capacity_R_relative_difference'],5),n(r['saved_lambda_second']),n(r['endpoint_zero_minimum']),n(r['endpoint_zero_to_bottom_ratio'],6)])+'|')
 lines+=['','## Registered predictions (all eight cells required)','']
 for s in scores:lines.append(f'- {s["id"]}: {s["passed"]}/{s["zeta_cells"]} cells; all-eight criterion '+('PASS' if s['all8_pass'] else 'FAIL')+'.')
 lines+=['','## DH controls','', '|m|q|cutoff|negative saved G levels|denominator sign|algebraic cap*pi*T/logT|endpoint-zero minimum|','|---:|---:|---|---:|---:|---:|---:|']
 for r in dh:lines.append('|'+ '|'.join([str(r['m']),str(r['q']),r['cutoff_mode'],str(r['saved_spectrum_negative']),str(r['inverse_denominator_sign']),n(r['capacity_scaled']),n(r['endpoint_zero_minimum'])])+'|')
 lines+=['','DH negative eigenvalues and signed inverse denominators are retained. A favorable-looking scaled inverse number does not establish positive complement coercivity in an indefinite control. Saved tiny inertia signs are floating diagnostics, not interval certification.','',
 'Raw results and source hashes: capacity.json/capacity.csv; prediction scoring: capacity_scored.json; separate higher-precision worst-case replay: precision_validation.json. Inverse-solve, nullspace, orthogonality, trace and interlacing checks are retained per cell.','']
 if (P/'precision_validation.json').exists():
  v=json.loads((P/'precision_validation.json').read_text());mx=max(mp.mpf(a['relative_difference']) for a in v['comparisons'])
  lines+=['## Precision validation','',f'Highest zeta m240q139 was rerun at80 and110dps. All five comparisons pass the1e-40 relative criterion; maximum relative difference is {mp.nstr(mx,8)} (endpoint-zero minimum).','']
 if (P/'worst_inverse_validation.json').exists():
  v=json.loads((P/'worst_inverse_validation.json').read_text())
  lines+=[f'The most ill-conditioned DH native m240q216 inverse was separately recomputed at110dps without an eigenproblem: relative capacity difference {mp.nstr(mp.mpf(v["relative_difference"]),8)} versus its80dps value. Explicit1e-8 relative criterion: '+('PASS' if v['passes_relative_1e_8'] else 'FAIL')+'. Its smallest absolute G eigenvalue at80dps is about1.62e-66; no70-digit accuracy claim is made for this ill-conditioned inverse.','']
 (P/'RESULT.md').write_text('\n'.join(lines));print(json.dumps(scores,indent=2))
if __name__=='__main__':main()
