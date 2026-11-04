"""Offline consistency/integrity checks for saved point replays and address lookups."""
from pathlib import Path
from datetime import datetime
import json,csv,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=100

def read(n):return json.loads((P/n).read_text())
def z(v):return mp.mpc(v['real'],v['imag'])
own=read('INDEPENDENT_RESULTS.json');app=read('APPENDIX_REPLAY.json');g=read('GATES.json');reg=read('PREREGISTRATION.json');a=read('ADDRESS_MATCHES.json')
assert own['status']=='PASS_DIAG_NOT_INTERVAL'and g['failure_count']==0 and len(own['records'])==len(app['records'])==10
assert g['gate_count']==288 and all(r['pass_gate']for r in g['gate_records'])and g['mathematical_field_comparison_count']==88 and g['all_mathematical_comparisons_pass']
assert datetime.fromisoformat(reg['registered_UTC'].replace('Z','+00:00'))<datetime.fromisoformat(own['started_UTC'])
b=(P/'PREDICTIONS.md').read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==reg['predictions_blob']=='4fcdbb980d1b2d55005bf26e681bc820c59e94ee'
for r in own['records']:
 tol=mp.mpf('1e-30')if r['dps']==45 else mp.mpf('1e-50');isplant=r['kind']=='PLANTED';errors=[]
 real=r['real_axis']if isplant else r['real_axis_DH'];assert abs(mp.mpf(real['defect']))<tol
 if not isplant:assert mp.mpf(r['functional_equation_relative_error'])<tol
 for s in r['samples']:
  eps=mp.mpf(s['epsilon']);node=s['plant'if isplant else'DH'];defect=mp.mpf(node['defect']);assert 2*eps<defect<6*eps;errors.append(abs(defect/(4*eps)-1))
  for key in [('plant'if isplant else'DH'),'zeta_control','curve_control']:
   q=s[key];M=z(q['M']);S=(M-1j)/(M+1j);lhs=abs(S)**2-1;rhs=-4*mp.im(M)/abs(M+1j)**2
   assert abs(lhs-mp.mpf(q['defect']))<tol and abs(rhs-mp.mpf(q['identity_rhs']))<tol and abs(lhs-rhs)<tol
   assert z(q['z']).imag>0
   if key.endswith('_control'):assert mp.mpf(q['defect'])<=tol
 assert errors[1]<errors[0]
assert a['source_saved_event_count']==18811 and len(a['summary_rows'])==28 and a['neighbor_rows_count']==66 and a['C4_addresses_with_hit_at_m2000']==3
neighbors=list(csv.DictReader((P/'ADDRESS_NEIGHBORS.csv').open()));assert len(neighbors)==66
for r in neighbors:
 assert 1<=int(r['j'])<=int(r['m'])and int(r['offset'])in[-1,0,1]
 if r['saved_event']=='False':assert not r['saved_Ajj']and not r['saved_minor_det']
 assert r['status']in['SAVED_EVENT','NO_SAVED_EVENT']
assert sum(r['saved_event']=='True'for r in neighbors)==11
for row in a['summary_rows']:
 L=mp.log(row['m']);j0=int(mp.nint(mp.mpf(row['address_gamma'])*L/(2*mp.pi)));assert j0==row['j0']
 assert row['valid_neighbors']==[j for j in [j0-1,j0,j0+1]if 1<=j<=row['m']]
 hits=[int(r['j'])for r in neighbors if r['address_gamma']==row['address_gamma']and int(r['m'])==row['m']and r['saved_event']=='True'];assert hits==row['event_j']
assert hashlib.sha256((P/'appendix_a.py').read_bytes()).hexdigest()=='0ce6fd6483229146c0af0fcff282ba472ea2aa3ccbfcd5939e5a0128cec6e5c5'
assert all(r['pass_gate']for r in read('PREDICTION_SCORES.json').values())
for line in(P/'SHA256SUMS').read_text().splitlines():
 expected,name=line.split('  ',1);assert hashlib.sha256((P/name).read_bytes()).hexdigest()==expected,name
print('PASS: registration; two10-record replays;288 gates;88 common fields;66 saved-neighbor rows/11events; exact appendix bytes; allSHA256')
