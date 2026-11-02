"""Saved-vector support probe. DIAGNOSTIC_NEVER_A_PROOF; no eigensolve."""
import csv,json,hashlib
from pathlib import Path
import mpmath as mp
mp.mp.dps=150
OUT=Path(__file__).resolve().parent; ROOT=OUT.parents[1]; LEDGER=ROOT/'ledger_diff'
fmt=lambda x:mp.nstr(x,40)
rows=[];bands=[];sources=[]
for p in sorted((LEDGER/'ledger_cells').glob('*.json')):
 d=json.loads(p.read_text());s=d['summary'];H=mp.mpf(s['H_original']);m=int(s['m']);a=d['atoms']
 # Verify source immutability against the saved producer provenance.
 src=LEDGER/d['source_file'];assert hashlib.sha256(src.read_bytes()).hexdigest()==d['source_sha256'],src
 total=mp.fsum(mp.mpf(z['raw_P']) for z in a)
 assert abs(total-mp.mpf(s['raw_P_total']))<mp.mpf('1e-110')
 npp=[z for z in a if z['sector']=='nonprimepower'];pos=mp.fsum(max(mp.mpf(z['raw_P']),0) for z in npp);neg=mp.fsum(min(mp.mpf(z['raw_P']),0) for z in npp);net=pos+neg
 case=p.stem;row=dict(case=case,world=s['world'],m=m,q=s['q'],cutoff_mode=s['cutoff_mode'],H=fmt(H),P_NPP=fmt(net),R_NPP=fmt(net/H),harmful_NPP_over_H=fmt(pos/H),favorable_NPP_over_H=fmt(neg/H),coefficient_positive_NPP_over_H=fmt(mp.fsum(mp.mpf(z['raw_P']) for z in npp if z['coefficient_sign']=='b_positive')/H),coefficient_negative_NPP_over_H=fmt(mp.fsum(mp.mpf(z['raw_P']) for z in npp if z['coefficient_sign']=='b_negative')/H),complement_minimum=s['complement_minimum']);rows.append(row)
 for k in range(4):
  zz=[z for z in npp if min(3,int(4*mp.log(int(z['n']))/mp.log(m)))==k]
  bands.append(dict(case=case,band=k,r_lo=str(k/4),r_hi=str((k+1)/4),P_NPP_over_H=fmt(mp.fsum(mp.mpf(z['raw_P']) for z in zz)/H),harmful_NPP_over_H=fmt(mp.fsum(max(mp.mpf(z['raw_P']),0) for z in zz)/H),atom_count=len(zz)))
 sources.append(dict(file=str(p.relative_to(ROOT)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),matched_source_sha256=d['source_sha256']))
for name,rr in [('features.csv',rows),('log_bands.csv',bands)]:
 with (OUT/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(rr[0]));w.writeheader();w.writerows(rr)
checks=[]
for q,m,op in [(41,80,'<'),(63,120,'>'),(65,120,'>')]:
 r=next(x for x in rows if x['world']=='dh' and x['m']==m and int(x['q'])==q);value=mp.mpf(r['R_NPP']);ok=value<mp.mpf('.75') if op=='<' else value>mp.mpf('.75');checks.append(dict(case=r['case'],prediction=f'R_NPP{op}0.75',R_NPP=r['R_NPP'],passed=ok))
result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',primary_pass=all(z['passed'] for z in checks),checks=checks,threshold='0.75',sources=sources,prereg_sha256=hashlib.sha256((OUT/'PREREGISTRATION.md').read_bytes()).hexdigest(),code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(OUT/'outcome.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('sources',)},indent=2))
for r in rows:print(r['case'],r['R_NPP'],r['complement_minimum'][:18])
