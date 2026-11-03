from pathlib import Path
import json,csv,hashlib,sys
import mpmath as mp
P=Path(__file__).resolve().parent;ROOT=Path('/workspace/conditioning_input');mp.mp.dps=100
summaries=list(csv.DictReader((P/'separator_summary.csv').open()));counts=list(csv.DictReader((P/'counts.csv').open()));k1=[];validation=[]
for s in summaries:
 w=s['world'];m=int(s['m']);data=json.loads((P/'cells'/f'{w}_m{m}.json').read_text());old=json.loads((ROOT/'C_conditioning/cells'/f'{w}_m{m}.json').read_text())
 for row in old['rows']:
  if row['variant']!='base':continue
  same=next((r for r in data['sectors']if r['q']==row['q']),None)
  if same:validation.append(dict(world=w,m=m,q=row['q'],cut=row['cut'],delta_difference=abs(same['delta']-row['delta']),guard=row['delta_numeric_radius']))
 r=next((r for r in data['sectors']if r['kappa_left_open']<1<=r['kappa_right_closed']),None)
 if r:k1.append(r)
with (P/'kappa_one.csv').open('w',newline='')as f:
 wr=csv.DictWriter(f,fieldnames=list(k1[0]));wr.writeheader();wr.writerows(k1)
prec=[]
for path in (P/'precision_replay/cells').glob('*.json'):
 new=json.loads(path.read_text());old=json.loads((P/'cells'/path.name).read_text());diff=max(abs(a['delta']-b['delta'])for a,b in zip(old['sectors'],new['sectors']));prec.append(dict(world=new['summary']['world'],m=new['summary']['m'],delta_max_difference_768_to1024_bits=diff,sector_statuses_identical=all(a['status']==b['status']for a,b in zip(old['sectors'],new['sectors']))))
(P/'VALIDATION.json').write_text(json.dumps(dict(base_projector_matches=len(validation),max_base_delta_difference=max(r['delta_difference']for r in validation),all_base_differences_within_inherited_radius=all(r['delta_difference']<=r['guard']for r in validation),precision_replays=prec),indent=2)+'\n')
dg=[]
for c in counts:
 w=c['world'];m=int(c['m']);d=m+1
 from scan_separator import events
 import gmpy2 as gp
 gp.get_context().precision=768;ev=events(ROOT,w);om=2*gp.const_pi()*m/gp.log(m);q=0
 for h,im,mult in ev:
  q+=mult
  if q>=d:break
 val=mp.mpf(c['minimum_eigenvalue']);guard=mp.mpf(c['roundoff_guard'])
 dg.append(dict(world=w,m=m,q0_kappa_right_closed=float(ev[0][0]/om),q0_r=d,q0_status='UNDEFINED_LAMBDA_r',J0_kappa_left_open=float(h/om),J0_delta=0,J0_lambda0=c['minimum_eigenvalue'],J0_status='VACUOUS_PASS_NUMERIC'if val>guard else('FAIL_NUMERIC'if val < -guard else'UNRESOLVED_ZERO_SIGN')))
with(P/'degenerate_sectors.csv').open('w',newline='')as f:
 wr=csv.DictWriter(f,fieldnames=list(dg[0]));wr.writeheader();wr.writerows(dg)
baseline=json.loads((P/'summary.json').read_text());k1summary={w:{cat:[r['m']for r in k1 if r['world']==w and r['lambda_r_category']==cat]for cat in ['NONPOSITIVE','POSITIVE_BELOW_C2','AT_OR_ABOVE_C2']}for w in ['zeta','plant','dh']}
(P/'kappa_one_summary.json').write_text(json.dumps(k1summary,indent=2)+'\n')
replay=json.loads((P/'DH53_MP_REPLAY.json').read_text());cr=json.loads((P/'cells/dh_m53.json').read_text());details=[]
for r in cr['sectors']:
 if r['status']=='UNRESOLVED_NUMERIC_FLOOR':
  match=next(x for x in replay['results']if x['q']==r['q']and x['dps']==160);delta=mp.mpf(match['delta']);details.append(dict(q=r['q'],r=r['r'],delta=str(delta),lambda_r=r['lambda_r'],gap=str(mp.mpf(str(r['lambda_r']))-delta),result='NO_REPLAY_SUPPORTED',baseline_status=r['status']))
(P/'DH53_DECISION.json').write_text(json.dumps(dict(baseline='UNRESOLVED_FLOAT_SOURCE',secondary_recipe_replay='NO_REPLAY_SUPPORTED',sectors=details,scope='Reconstructed same source recipe, not byte-identical archived MP source; no interval bounds.'),indent=2)+'\n')
print('Validation',len(validation),'maxdiff',max(r['delta_difference']for r in validation),'precision replays',len(prec));print('kappa1 belowC2',{w:k1summary[w]['POSITIVE_BELOW_C2']for w in k1summary})
