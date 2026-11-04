"""Offline addendum sign/ratio/source checks; no new numerical scans."""
from pathlib import Path
import csv,json,gzip,hashlib
from decimal import Decimal
import mpmath as mp
P=Path(__file__).resolve().parents[1];mp.mp.dps=80

def read(n):return json.loads((P/n).read_text())
def rows(n):return list(csv.DictReader((P/n).open()))
def close(a,b,tol='1e-60'):assert abs(mp.mpf(a)-mp.mpf(b))<mp.mpf(tol)*max(1,abs(mp.mpf(a)),abs(mp.mpf(b)))
reg=read('ADD_PREREGISTRATION.json');pred=(P/'PREDICTIONS.md').read_bytes();assert hashlib.sha1(b'blob '+str(len(pred)).encode()+b'\0'+pred).hexdigest()==reg['prediction_blob']=='0e7307bf6b1345b61e6ada0d2476a2bf264f8f5e'
grid=[16,40,80,160,300,1000,2000];rs=rows('ADD_SECOND_RUNG.csv');assert len(rs)==2*sum(grid)
for w in ['zeta','dh']:
 for m in grid:assert {int(r['j'])for r in rs if r['world']==w and int(r['m'])==m}==set(range(1,m+1))
for r in rs:
 a,b,d=map(mp.mpf,[r['A00'],r['A0j'],r['Ajj']]);det=a*d-b*b;rat=b*b/(a*d)
 close(det,r['determinant']);close(rat,r['raw_ratio']);assert(r['PSD_minor_pass']=='True')==(a>=0 and d>=0 and det>=0)
 if r['world']=='zeta':assert a>0 and d>0 and det>0 and rat<1
s=read('ADD_SECOND_RUNG.json');assert s['bits']>=200 and s['confirmation_bits']>=250 and s['all_confirmation_signs_agree']
assert len(s['critical_confirmation'])==36 and all(r['bits']>=250 for r in s['critical_confirmation'])
assert s['DH_first_failure']['m']==75 and s['DH_first_failure']['failed_rows'][0]['j']==58
raw=read('ADD_SECOND_RUNG_RAW.json');first=raw['critical_confirmations'][0];assert first['m']==463 and first['j']==234 and first['bits']>=250
assert mp.mpf(first['raw_ratio'])>1 and mp.mpf(first['A00'])>0 and mp.mpf(first['Ajj'])>0 and mp.mpf(first['determinant'])<0
assert raw['integer_m_covered']==[2,463]and raw['near_one_count']==1 and not raw['disagreements']
d=read('ADD_DH_DENSE.json');dense=rows('ADD_DH_DENSE.csv');assert [int(r['m'])for r in dense]==list(range(2,2001))
assert d['first_raw_crossing_screen']['m']==463 and d['first_PSD_failure_screen']['m']==75 and d['all_selected_engine_gates_pass']
assert d['new_target_row_count']==sum(int(r['raw_above_guard_count'])for r in dense if int(r['m'])>=464)==11
assert sum(int(r['m'])for r in dense)==2000999
assert all(r['bits']>=200 and mp.mpf(r['raw_ratio'])>1 for r in d['new_selected_confirmations'])
max_r=max(d['new_selected_confirmations'],key=lambda r:mp.mpf(r['raw_ratio']));assert max_r['m']==1800 and max_r['j']==137
summary=rows('ADD_SUMMARY.csv');assert len(summary)==14
for r in summary:
 if r['world']=='zeta':assert r['j']=='1'and r['S2_near_14_13']=='False'and r['failed_corner_minors']=='0'
checks=read('ADD_DH_CHECKS.json');dh=read('ADD_DH_SUMMARY.json');assert dh['evaluated_integers']==9999999 and dh['negative_count']==0 and dh['first_negative_m']==0 and dh['coefficient_bits']==192
assert mp.mpf(checks['max_native_difference'])<mp.mpf('1e-14')and len(checks['grid_crosscheck'])==7
for r in checks['grid_crosscheck']:assert abs(mp.mpf(r['difference']))<mp.mpf('1e-45')
for r in checks['coefficient_spots']:assert abs(mp.mpf(r['difference']))<mp.mpf('1e-45')*max(1,abs(mp.mpf(r['b_recursion_mp60'])))
assert checks['minimum_neighborhood_winner']['m']==dh['minimum_m']==9356256 and mp.mpf(checks['minimum_neighborhood_winner']['Psi_mp60'])>0
assert read('ADD_SECOND_RUNG_SOURCECHECK.json')['status']=='PASS'
prev_m=0;prev_v=Decimal('Infinity');nr=0;h=hashlib.sha256()
with gzip.open(P/'ADD_DH_RECORD_MINIMA.csv.gz','rb')as f:
 header=next(f);h.update(header)
 for line in f:
  h.update(line);m,_,v=line.decode().strip().split(',');assert int(m)>prev_m and Decimal(v)<prev_v;prev_m,prev_v=int(m),Decimal(v);nr+=1
assert nr==dh['record_count']==55052 and prev_m==9356256
original=next(r for r in read('ADD_LOCAL_DATA.json')if r['local_path'].endswith('ADD_DH_RECORD_MINIMA.csv'));assert h.hexdigest()==original['sha256']
g=read('ADD_GATES.json');assert g['S1']['score']=='PASS_DIAGNOSTIC'and g['S2']['score']=='FAIL_DIAGNOSTIC'and g['H1']['score']=='FAIL_DIAGNOSTIC'and not g['RH_export']
for line in(P/'SHA256SUMS').read_text().splitlines():
 expected,name=line.split('  ',1);assert hashlib.sha256((P/name).read_bytes()).hexdigest()==expected,name
print('PASS: original prediction plus addendum blob; 7192 highprecision grid pairs; 2,000,999 dense DH pairs; sign-aware first75/463; ownDH1e7 corner checks and55,052records; allSHA256')
