"""Frozen published sectors/censuses. No source or frame construction."""
from pathlib import Path
import os,csv,json,math,functools,bisect
from decimal import Decimal,localcontext
P=Path(__file__).resolve().parent
BASE=Path(os.environ.get('PAIR_BASE','/workspace/stiffness/repo/docs/routeB_bus/stitch_conditioning_2026-11-03/zero_separator'));BUS=BASE.parents[1]
MID=BASE/'extension_121_300';HIGH=BASE/'spike_trend_310_600'
MS=list(range(16,301))+list(range(310,601,10));THETAS=[.5,.6,.75]
def exact_beta(s):
 with localcontext()as c:
  c.prec=max(100,len(s)+4);return str(Decimal(s)-Decimal('0.5'))
def region(m):return 'low'if m<=120 else'mid'if m<=300 else'high'
def packet(m):return BASE if m<=120 else MID if m<=300 else HIGH
@functools.lru_cache(None)
def events(world,rg):
 if world in ['zeta','plant']:
  f=BUS/'capacity_matrix_2026-11-02/zeros.csv'if rg=='low'else(MID if rg=='mid'else HIGH)/'zeta_zeros.csv'
  ev=[dict(gamma=float(x['gamma']),beta=0.,beta_decimal='0',mult=1,gamma_decimal=x['gamma'],type='LINE')for x in csv.DictReader(f.open())]
 else:
  f=BUS/'fake_worlds_2026-11-02/dh_zeros.json'if rg=='low'else(MID/'dh_census/dh_zeros_600_200dps.json'if rg=='mid'else HIGH/'dh_census/dh_zeros_900_200dps.json');z=json.loads(f.read_text());ev=[dict(gamma=float(x['gamma']),beta=0.,beta_decimal='0',mult=1,gamma_decimal=x['gamma'],type='LINE')for x in z['critical_line_zeros']]+[dict(gamma=float(x['gamma']),beta=float(x['sigma_right'])-.5,beta_decimal=exact_beta(x['sigma_right']),mult=2,gamma_decimal=x['gamma'],type='QUARTET')for x in z['off_line_pairs']]
 if world=='plant':ev.append(dict(gamma=2*math.pi/math.log(2),beta=.25,beta_decimal='0.25',mult=2,gamma_decimal='2*pi/log(2)',type='PLANTED_QUARTET'))
 ev.sort(key=lambda x:x['gamma']);q=0
 for i,x in enumerate(ev):q+=x['mult'];x.update(ordinal=i+1,q_after=q)
 return ev
@functools.lru_cache(None)
def event_pairs(world,rg):
 ev=events(world,rg);rows=[]
 for i,(a,b)in enumerate(zip(ev,ev[1:])):
  center=(a['gamma']+b['gamma'])/2;log=math.log(center/(2*math.pi));spacing=2*math.pi/log if log>0 else None
  if spacing is None:continue
  rows.append(dict(pair_index=i,left_ordinal=i+1,right_ordinal=i+2,left_gamma=a['gamma'],right_gamma=b['gamma'],left_mult=a['mult'],right_mult=b['mult'],left_type=a['type'],right_type=b['type'],split_q=a['q_after'],pair_midpoint=center,gap=b['gamma']-a['gamma'],local_spacing=spacing,normalized_gap=(b['gamma']-a['gamma'])/spacing))
 return rows
@functools.lru_cache(None)
def dataset():
 out={};low_summary={(x['world'],int(x['m'])):x for x in csv.DictReader((BASE/'separator_summary.csv').open())};low_sectors={}
 for x in csv.DictReader((BASE/'all_sectors.csv').open()):
  if x['intersects_kappa_ge1']!='1':continue
  w=x['world'];m=int(x['m']);g=float(x['numeric_guard']);s=dict(q=int(x['q']),r=int(x['r']),left=float(x['kappa_left_open']),right=float(x['kappa_right_closed']),kappa=max(1,float(x['kappa_mid'])),lambda_r=float(x['lambda_r']),delta=float(x['delta']),gap=float(x['gap']),guard=g,status=x['status'],kind='evaluated',method='PINNED_FULL_SECTOR_CSV');low_sectors.setdefault((w,m),[]).append(s)
 for key,ss in low_sectors.items():
  a=low_summary[key];bestq=key[1]+1-int(a['best_ge1_r']);best=next(s for s in ss if s['q']==bestq);guard=max(s['guard']for s in ss);out[key]=dict(world=key[0],m=key[1],region='low',sectors=sorted(ss,key=lambda x:x['q']),guard=guard,original_status=a['separator_kappa_ge1'],original_gap=float(a['best_ge1_gap']),original_q=bestq,original_best=best,original_lower=best['gap']-guard,original_upper=max(s['gap']for s in ss)+guard,nminus_lower=int(a['n_minus_lower']))
 for sub in [MID,HIGH]:
  for f in(sub/'scan_cells').glob('*.json'):
   d=json.loads(f.read_text());a=d['summary'];m=int(a['m']);w=a['world'];g=float(a['numeric_guard']);ss=[]
   for kind,rs in [('evaluated',d['evaluated']),('bounded',d['bounded'])]:
    for x in rs:
     s=dict(q=int(x['q']),r=int(x['r']),left=float(x['kappa_left_open']),right=float(x['kappa_right_closed']),kappa=max(1,float(x.get('kappa_representative',(x['kappa_left_open']+x['kappa_right_closed'])/2))),lambda_r=float(x['lambda_r']),guard=g,status=x['status'],kind=kind,method=x['method'])
     if kind=='evaluated':s.update(delta=float(x['delta']),gap=float(x['gap']))
     else:s['upper']=float(x['gap_upper_bound'])
     ss.append(s)
   best=next(x for x in ss if x['q']==int(a['best_q']));out[w,m]=dict(world=w,m=m,region=region(m),sectors=sorted(ss,key=lambda x:x['q']),guard=g,original_status=a['separator_kappa_ge1'],original_gap=float(a['best_gap']),original_q=int(a['best_q']),original_best=best,original_lower=float(a['max_gap_lower_bound']),original_upper=float(a['max_gap_upper_bound']),nminus_lower=int(a['n_minus_lower']))
 assert len(out)==945
 # Cross-check every archived sector against its OWN atomic census.
 for (w,m),d in out.items():
  ev=events(w,region(m));qmap={x['q_after']:i for i,x in enumerate(ev)};Om=2*math.pi*m/math.log(m)
  for s in d['sectors']:
   assert s['q']in qmap,(w,m,s['q']);i=qmap[s['q']];assert i+1<len(ev),(w,m,i)
   assert abs(s['left']-ev[i]['gamma']/Om)<1e-11,(w,m,s,ev[i]);assert abs(s['right']-ev[i+1]['gamma']/Om)<1e-11,(w,m,s,ev[i+1]);s['left_event']=i+1
 return out

def pairs_for(w,m,theta):
 d=dataset()[w,m];Om=2*math.pi*m/math.log(m);T=Om*d['original_best']['kappa'];rows=[]
 for p in event_pairs(w,region(m)):
  if p['normalized_gap']>=theta:continue
  po=abs(p['pair_midpoint']-Om)/p['local_spacing'];pt=abs(p['pair_midpoint']-T)/p['local_spacing']
  if min(po,pt)>2:continue
  rows.append(dict(world=w,m=m,theta=theta,region=region(m),**p,Omega=Om,original_T=T,distance_to_Omega_spacings=po,distance_to_T_spacings=pt,near_Omega=po<=2,near_original_T=pt<=2,straddles_Omega=p['left_gamma']<Om<=p['right_gamma'],straddles_original_optimum=p['split_q']==d['original_q'],both_in_original=d['original_q']>p['split_q'],both_out_original=d['original_q']<p['split_q'],hermite_block_type='LINE_2X2'if p['left_mult']==p['right_mult']==1 else'QUARTET_4X4'if p['left_mult']==p['right_mult']==2 else'MIXED_3X3_NOT_NUMERICALLY_TESTED'))
 return rows

def write_csv(name,rows):
 rows=list(rows);keys=list(dict.fromkeys(k for r in rows for k in r))
 with(P/name).open('w',newline='')as f:
  w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
if __name__=='__main__':
 d=dataset();rows=[p for w,m in d for theta in THETAS for p in pairs_for(w,m,theta)];write_csv('PAIRS.csv',rows);print('945cells allsector/census gates pass;',len(rows),'pair records')
