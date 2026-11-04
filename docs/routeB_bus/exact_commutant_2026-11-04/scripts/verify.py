#!/usr/bin/env python3
"""Offline verification of Gate0, control receipts and analytical scalar rows."""
from pathlib import Path
from fractions import Fraction
from datetime import datetime,timedelta
import csv,json,hashlib
import mpmath as mp
P=Path(__file__).resolve().parents[1];mp.mp.dps=80

def read(n):return json.loads((P/n).read_text())
def close(a,b):assert abs(mp.mpf(a)-mp.mpf(b))<mp.mpf('1e-74'),(a,b)
def dt(t):return datetime.fromisoformat(t.replace('Z','+00:00'))
g=read('GATE0.json');c=read('CONTROLS.json');r=read('PREREGISTRATION.json');s=read('SCORES.json')
assert g['status']=='PASS' and g['mpmath_dps']>=50 and [x['m']for x in g['rows']]==[16,80,300]
assert g['registration_commit']==r['commit'] and dt(r['committed_UTC'])<dt(g['started_UTC'])
assert dt(g['started_UTC'])+timedelta(seconds=g['seconds'])<dt(c['started_UTC'])
pred=(P/'PREDICTIONS.md').read_bytes();assert hashlib.sha1(b'blob '+str(len(pred)).encode()+b'\0'+pred).hexdigest()==r['predictions_blob']=='4bbcdb94bfdc2b3165d7dc4db6d4f0c80a9f376b'
for x in g['rows']:
 L=mp.log(x['m']);close(x['L'],L)
 close(mp.mpf(x['H00'])+mp.mpf(x['P00'])-mp.mpf(x['B00']),x['A00_scalar'])
 close(x['A00_pinned_builder'],x['A00_scalar']);close(2*mp.mpf(x['Suzuki_Psi'])/L,x['two_Psi_over_L'])
 close(x['P00'],8*(mp.exp(L/2)+mp.exp(-L/2)-2)/L)
 for a,b in [('H00','Suzuki_gamma_scaled'),('P00','Suzuki_pole_scaled')]:close(x[a],x[b])
 close(-mp.mpf(x['B00']),x['Suzuki_prime_signed_scaled'])
 assert all(abs(mp.mpf(v))<=mp.mpf('1e-40')for v in x['differences'].values()) and x['pass_gate']
 assert x['builder_metadata']['bits']==320
p=c['positive'];n=c['negative'];assert c['mpmath_dps']>=50 and not p['passes_requested_control']
close(mp.mpf(p['commutator_Frobenius'])/(mp.mpf(p['D_Frobenius'])*mp.mpf(p['K_Frobenius'])),p['fixed_Slepian_normalized_residual'])
assert mp.mpf(p['fixed_Slepian_normalized_residual'])>mp.mpf('1e-25')
assert mp.mpf(p['commutator_entry_01'])<0 and p['m']==16 and p['rho']=='1'
assert all(abs(mp.mpf(x['difference']))<mp.mpf('1e-70')for x in p['D_entry_spot_checks'])
assert mp.mpf(n['commutator_residual'])==0 and n['seed']==20261104;close(n['D_norm'],1)
assert not c['CCM_scan_run']and not c['non_scalar_commutant_scan_run']and not g['scan_run']
rows=list(csv.DictReader((P/'R.csv').open()));assert len(rows)==30
assert {(int(x['m']),x['piece'])for x in rows}=={(m,w)for m in [16,40,100,300,1000]for w in ['H','P','H+P','B','A','A+Q']}
for x in rows:
 m=int(x['m']);assert x['r_exact']=='0'and x['scan_status']=='VOID_POSITIVE_CONTROL_FAILURE'
 assert all(x[k]=='0'for k in ['a0','a2','a4','b2','b4'])and x['b0_exact']==f'1/sqrt({m+1})'
 assert Fraction(m+1,m+1)==1 and x['D_Frobenius_exact']=='1'and x['r_basis']=='EXACT_SCALAR_WITNESS_NOT_NUMERIC_SCAN'
assert not s['CCM_scan_run']and not s['repaired_metric_run']and s['R6']['universal_or_non_scalar_version']=='NOT_TESTED'
assert s['G0']['score']=='PASS'and s['R1']['score']=='FALSE_UNDER_LITERAL_METRIC'
for line in(P/'SHA256SUMS').read_text().splitlines():
 h,name=line.split('  ',1);assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h,name
print('PASS: registration precedes all numerical work; three source gates; failed controls; thirty analytical scalar rows; no scan; packet hashes')
