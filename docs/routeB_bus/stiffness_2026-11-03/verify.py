"""Readback verification of delivered scalar/vector evidence; no dense replay."""
from pathlib import Path
import hashlib,json,csv,gzip,tarfile,io
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=120
for line in(P/'SHA256SUMS').read_text().splitlines():
 h,n=line.split('  ',1);assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h,n
arc=json.loads((P/'BINARY_ARCHIVE.json').read_text());pieces=[]
for x in arc['parts']:
 b=(P/x['path']).read_bytes();assert len(b)==x['bytes']and hashlib.sha256(b).hexdigest()==x['sha256'];pieces.append(b)
b=b''.join(pieces);assert hashlib.sha256(b).hexdigest()==arc['sha256'];expected={x['path']:x for x in arc['members']};gates=0
with tarfile.open(fileobj=io.BytesIO(b),mode='r:gz')as t:
 assert len(t.getmembers())==24
 for m in t.getmembers():
  r=expected[m.name];b=t.extractfile(m).read();assert len(b)==r['bytes']and hashlib.sha256(b).hexdigest()==r['sha256'];d=json.loads(b);assert d['P1_gate'];assert d['source_reconstruction_max_entry']<=d['rho']
  if d['face_gate']:
   gates+=1;assert 'P2'in d and'P3'in d;p=d['P3'];assert 'dual_Y'not in p;assert p['primal_value']>=0 and p['primal_budget_norm']<=1+1e-10;assert p['primal_gauge_residual']<1e-10
   if p['dual_upper_envelope']is not None:assert p['dual_upper_envelope']+1e-7*max(1,p['scale'])>=p['primal_value']
  else:assert d['P2_status']==d['P3_status']=='STOPPED_FAILED_GATE'
assert gates==10
for m,kern in[(16,7),(24,10),(40,13)]:
 d=json.loads((P/f'mp_prices_m{m}.json').read_text());f=d['literal_face'];ball=f['P3_ball'];assert d['P1_gate_pass']and f['gate_pass'];assert d['selected_face_size']==1 and f['P2_full_map']['kernel_dimension']==kern
 pp=[mp.mpf(x['price'])for x in f['P3_optimizer_labeled']];tt=[mp.mpf(x['t'])for x in f['P3_optimizer_labeled']];opt=mp.mpf(ball['scalar_analytic_ball_optimum']);mean=mp.fsum(pp)/len(pp)
 assert abs(mp.sqrt(mp.fsum((x-mean)**2 for x in pp))-opt)<mp.mpf('1e-105');assert abs(mp.fsum(tt))<mp.mpf('1e-105');assert abs(mp.fsum(x*x for x in tt)-1)<mp.mpf('1e-105');assert abs(mp.fsum(x*y for x,y in zip(pp,tt))-opt)<mp.mpf('1e-105');assert opt>2
 assert not ball['dual_Y_valid_as_annihilating_stress'];assert mp.mpf(ball['dual_stress_price_residual_norm'])>2
 gg=next(x for x in d['P4_intervals']if x['knob']=='C_Gamma');pole=next(x for x in d['P4_intervals']if x['knob']=='C_pole');assert gg['raw_knob_inertia']['negative']>0 and gg['raw_knob_inertia']['positive']>0;assert pole['PSD_pole_structural_upper_infinity']
 p5=json.loads((P/f'p5_mp_m{m}.json').read_text());assert p5['a0_equals_2A_exact_by_preserved_baseline'];assert all(mp.mpf(x)<0 for x in p5['quiet_basis_diagonal']);assert max(mp.mpf(x)for x in p5['quiet_curvature_eigenvalues'])>0;assert mp.mpf('.5')<=mp.mpf(p5['full_over_registered'])<=2
 for key in['full_root','quiet_trial_root']:
  assert mp.mpf(p5[key].get('threshold_eigenvalue_lower',p5[key]['value_lower']))>mp.mpf('1e-114');assert mp.mpf(p5[key].get('threshold_eigenvalue_upper',p5[key]['value_upper']))< -mp.mpf('1e-114')
s4=json.loads((P/'p5_S4_FRAME_CONFIRMATION.json').read_text());assert not s4['saved_frames_S4_all_pilots_pass'];cc=next(x for x in s4['cells']if x['m']==24);assert cc['positive_columns_zero_based']==[16]and mp.mpf(cc['positive_values'][0])>1 and mp.mpf(cc['projected_positive_values'][0])>1;assert mp.mpf(cc['maximum_normalized_projection_difference'])<mp.mpf('1e-14')
assert len(list(csv.DictReader((P/'SUMMARY.csv').open())))==27
assert len(list(csv.DictReader((P/'mp_prices_inertias.csv').open())))==33
assert len(json.loads((P/'REGENERATED_ARRAYS.json').read_text()))==43
frames=json.loads((P/'FRAME_REPLAY_CHECK.json').read_text());assert len(frames)==16 and max(x['normalized_constraint_residual']for x in frames)<1e-12
j=json.loads((P/'p5_VALIDATION.json').read_text());assert len(j['cells'])==11
for r in j['cells']:assert hashlib.sha256((P/r['file']).read_bytes()).hexdigest()==r['sha256']
assert hashlib.sha256((P/'p5.py').read_bytes()).hexdigest()==j['code_sha256']
controls=list(csv.DictReader((P/'p5_controls.csv').open()));assert all(x['negative_detected']=='True'for x in controls if x['world']in['double2','pinned_low_quartet_plant']);assert all(x['negative_detected']=='True'for x in controls if x['world']=='dh'and int(x['m'])>=80)
print('PASS:24binary cells,3MP pilots,11dial cells; gates,prices,kernels,one-sided pole and43local hashes')
