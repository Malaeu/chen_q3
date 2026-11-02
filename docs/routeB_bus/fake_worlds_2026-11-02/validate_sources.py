"""DIAGNOSTIC_NEVER_A_PROOF: reproduce fixed-Q matrix-source validation.
Run: uv run --with mpmath python3 validate_sources.py
Only quiet_source_validation.json is written; input data are read-only.
"""
import json,hashlib,sys
from pathlib import Path
import mpmath as mp
mp.mp.dps=160
P=Path(__file__).resolve().parent
rows=[]
for m in (20,40,60,80,100,120):
 p=P/f'quiet_m{m}_k11.json'
 if not p.exists():continue
 quiet=json.loads(p.read_text())
 a=P/'matrix_cells'/f'dh_m{m}_dps80_gl96.json';b=P/'matrix_cells'/f'dh_m{m}_dps120_gl128.json'
 low=json.loads(a.read_text());high=json.loads(b.read_text());A=mp.matrix(low['A']);B=mp.matrix(high['A']);D=B-A;bound=mp.norm(D)
 el=list(map(mp.mpf,low['lambda_']));eh=list(map(mp.mpf,high['lambda_']))
 for key,c in quiet['cache'].items():
  Q=mp.matrix(c['Q']);gram=Q.T*Q
  qev=mp.eigsy(gram,eigvals_only=True);qnorm=mp.sqrt(qev[len(qev)-1]) if Q.cols else mp.mpf(0)
  def opdelta(K):
   if not Q.cols:return mp.mpf(0)
   v=mp.eigsy((K*Q).T*(K*Q),eigvals_only=True)
   return mp.sqrt(max(mp.mpf(0),v[len(v)-1]))
  dl=opdelta(A);dh=opdelta(B);stored=mp.mpf(c['delta']);factor=mp.mpf('1.000001');ml=dl*factor;mh=dh*factor
  gap=min(abs(v-ml) for v in el);gap_hi=min(abs(v-mh) for v in eh)
  perturb=bound*(1+factor*qnorm)
  f=lambda x:mp.nstr(x,130)
  rows.append(dict(m=m,q=int(key),dim_J=Q.cols,evaluation_dps=160,matrix_source_dps=[80,120],fixed_Q_source_dps=quiet['dps'],delta_A80=f(dl),delta_A120=f(dh),delta_absolute_change=f(abs(dl-dh)),stored_delta_replay_error=f(abs(stored-dl)),matrix_difference_Frobenius_bound=f(bound),Q_operator_norm=f(qnorm),delta_change_bound=f(bound*qnorm),bound_over_delta=f(bound/dl) if dl else None,count_threshold_A80=f(ml),count_threshold_A120=f(mh),nearest_eigenvalue_gap_A80=f(gap),nearest_eigenvalue_gap_A120=f(gap_hi),combined_Weyl_and_threshold_perturbation_bound=f(perturb),combined_bound_over_count_gap=f(perturb/gap),count_A80=sum(v<ml for v in el),count_A120=sum(v<mh for v in eh),delta_change_within_bound=bool(abs(dl-dh)<=bound*qnorm),count_preserved_by_computed_perturbation_margin=bool(perturb<gap),source_sha256={str(x.relative_to(P)):hashlib.sha256(x.read_bytes()).hexdigest() for x in (p,a,b)}))


for row in rows:
 quiet=json.loads((P/f"quiet_m{row['m']}_k11.json").read_text())
 c=quiet['cache'][str(row['q'])]
 row.update(stored_sigma_min=c['sigma_min'],sigma_min_below_1e_minus60=mp.mpf(c['sigma_min'])<mp.mpf('1e-60'))
metadata=json.loads("{\"status\":\"DIAGNOSTIC_NEVER_A_PROOF\",\"scope\":\"Fixed stored Q only: compare 80-dps and 120-dps DH matrices; no zero-location or kernel-conditioning validation.\",\"evaluation_dps\":160,\"method\":\"Recompute delta_low=||A80 Q||_2 and delta_high=||A120 Q||_2. Bound ||A120-A80||_2 by its Frobenius norm B. Then |delta_high-delta_low| <= B||Q||_2. With mu=1.000001 delta, combined eigenvalue/threshold perturbation is bounded by B(1+1.000001||Q||_2). Compare with the nearest A80 eigenvalue distance to mu_low, and explicitly recount at both thresholds.\",\"limitations\":[\"Computed multiprecision matrix comparisons are diagnostic, not outward-rounded interval bounds.\",\"These calculations keep Q fixed. They do not validate the DH zero census, zero coordinates, rank, or the actual interpolation kernel.\",\"A small singular value can amplify zero-coordinate errors independently of the matrix-source perturbations tested here.\"],\"metadata_note\":\"Root renamed ordinary_gram_min to ordinary_gram_min_on_J_perp for accuracy; numerical data unchanged; source hashes refreshed.\"}")
result=dict(metadata,rows=rows,
 all_six_counts_unchanged=all(r['count_A80']==r['count_A120'] for r in rows),
 all_delta_changes_within_computed_bound=all(r['delta_change_within_bound'] for r in rows),
 all_count_margins_exceed_computed_source_perturbation=all(r['count_preserved_by_computed_perturbation_margin'] for r in rows))
out=P/'quiet_source_validation.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(out)

