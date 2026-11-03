"""Bounded Hermite-coordinate pilots; fixed source, q, r and lambda_r.
No dropped constraints: sum/divided difference is an invertible row transform.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json,csv,time,hashlib
import numpy as np
import scipy.linalg as la
import baseline_replay as base
G=base.source.g;NATIVE=base.native_frame;LOCAL=base.LOCAL;OUT=base.OUT

def own_census(world,m):
 B=base.ROOT.parents[1]
 if world in ('zeta','plant'):
  path=B/'capacity_matrix_2026-11-02/zeros.csv'if m<=120 else(base.EXT if m<=300 else base.HIGH)/'zeta_zeros.csv'
  ev=[(G.mpfr(x['gamma']),G.mpfr(0),1)for x in csv.DictReader(path.open())]
 else:
  path=B/'fake_worlds_2026-11-02/dh_zeros.json'if m<=120 else(base.EXT/'dh_census/dh_zeros_600_200dps.json'if m<=300 else base.HIGH/'dh_census/dh_zeros_900_200dps.json')
  zz=json.loads(path.read_text());ev=[(G.mpfr(x['gamma']),G.mpfr(0),1)for x in zz['critical_line_zeros']]+[(G.mpfr(x['gamma']),G.mpfr(x['sigma_right'])-G.mpfr('.5'),2)for x in zz['off_line_pairs']]
 if world=='plant':ev.append((2*G.const_pi()/G.log(2),G.mpfr('.25'),2))
 return sorted(ev),path

def physical_rows(world,m,q):
 G.get_context().precision=768;L=G.log(m);freq=[(2*G.const_pi()*j/L)**2 for j in range(m+1)];ds=[G.mpfr(1)]+[G.sqrt(2)]*m;rows=[];included=[]
 events,censuspath=own_census(world,m)
 for i,(h,im,mult)in enumerate(events):
  if len(rows)>=q:break
  t=G.mpc(h,im);factor=2*t*G.sin(t*L/2)/G.sqrt(L)
  rr=[factor*ds[j]/(t*t-freq[j])for j in range(m+1)];offset=len(rows);rows.append([z.real for z in rr])
  if mult==2:rows.append([z.imag for z in rr])
  included.append(dict(event_index=i,ordinal=i+1,h=h,im=im,mult=mult,row_start=offset))
 assert len(rows)==q,('q would split orbit',world,m,q,len(rows))
 return rows,included,censuspath

def candidate_pairs(included,m,cutoff=None):
 G.get_context().precision=768;Om=2*G.const_pi()*m/G.log(m);out=[]
 for left,right in zip(included,included[1:]):
  if left['mult']!=right['mult']:continue
  mid=(left['h']+right['h'])/2;spacing=2*G.const_pi()/G.log(mid/(2*G.const_pi()));ratio=(right['h']-left['h'])/spacing
  near_om=abs(mid-Om)/spacing<=2;near_cut=abs(mid-G.mpfr(str(cutoff)))/spacing<=2 if cutoff is not None else False
  out.append(dict(left=left,right=right,gap=right['h']-left['h'],midpoint=mid,local_mean_spacing=spacing,normalized_gap=ratio,near_omega=bool(near_om),near_original_cutoff=bool(near_cut)))
 return out

def quiet(rows):
 uf,piv=NATIVE.frame(rows,768);whole,_=la.qr(uf.T,mode='full');return whole[:,len(rows):],float(la.norm(uf@uf.T-np.eye(len(rows)),2)),float(min(piv))

def run(world,m,q,forced_ordinals=None,cutoff=None):
 if json.loads((OUT/'baseline_manifest.json').read_text())['status']!='SEVEN_BASELINE_GATES_PASS':raise ArithmeticError('baseline gate absent')
 t0=time.monotonic();path=LOCAL/'matrices'/f'{world}_m{m}.npz';z=np.load(path);A=z['A'];ev=z['eigenvalues'];r=m+1-q;lam=float(ev[r]);rows,inc,censuspath=physical_rows(world,m,q);pairs=candidate_pairs(inc,m,cutoff)
 if forced_ordinals:
  pp=[p for p in pairs if(p['left']['ordinal'],p['right']['ordinal'])==tuple(forced_ordinals)]
  assert len(pp)==1;pair=pp[0]
 else:
  nearby=[p for p in pairs if p['near_omega']or p['near_original_cutoff']]
  pair=min(nearby,key=lambda p:p['normalized_gap'])if nearby else None
 Q,orth,pivot=quiet(rows);delta=float(la.norm(A@Q,2));norm=float(la.norm(A,2));guard=max(float(z['numeric_radius']),1000*np.finfo(float).eps*(m+1)*max(1,norm));out=[];transform=None
 for theta in [.5,.6,.75]:
  active=pair is not None and pair['normalized_gap']<G.mpfr(str(theta))
  if active:
   if transform is None:
    rr=[x[:]for x in rows];i=pair['left']['row_start'];j=pair['right']['row_start'];mult=pair['left']['mult'];gap=pair['gap']
    for branch in range(mult):
     a=rows[i+branch];b=rows[j+branch];rr[i+branch]=[(v+w)/2 for v,w in zip(a,b)];rr[j+branch]=[(w-v)/gap for v,w in zip(a,b)]
    Qh,orthh,pivh=quiet(rr);dh=float(la.norm(A@Qh,2));pd=float(la.norm(Q@Q.T-Qh@Qh.T,2));transform=(dh,pd,orthh,pivh)
   dh,pd,orthh,pivh=transform
  else:dh,pd,orthh,pivh=delta,0.,orth,pivot
  resolved=delta>guard
  item=dict(world=world,m=m,q=q,r=r,theta=theta,status='TRANSFORM_EXECUTED'if active else('NO_ADMISSIBLE_INCLUDED_NEAR_PAIR'if pair is None else'PAIR_NOT_BELOW_THETA_IDENTITY'),both_events_included=pair is not None,pair_ordinals=[pair['left']['ordinal'],pair['right']['ordinal']]if pair else None,event_multiplicity=pair['left']['mult']if pair else None,pair_normalized_gap=float(pair['normalized_gap'])if pair else None,normalization='gap/(2pi/log(midgamma/(2pi)))',physical_scalar_before_combinations=True,complex_real_imag_scale='same original scan real/imag rows; no row-count or orbit splitting',delta_original=delta,delta_hermite=dh,absolute_delta_difference=abs(dh-delta),relative_delta_difference=abs(dh-delta)/abs(delta)if resolved else None,relative_scoring='RESOLVED'if resolved else'UNRESOLVED_AT_ORIGINAL_NUMERIC_FLOOR',projector_difference=pd,lambda_r=lam,lambda_r_reused_identically=True,source_guard=guard,original_frame_orthogonality=orth,hermite_frame_orthogonality=orthh,original_min_relative_mgs_pivot=pivot,hermite_min_relative_mgs_pivot=pivh,source_npz_sha256=base.sha(path),zero_census_path=str(censuspath),zero_census_sha256=base.sha(censuspath),own_census_region='low'if m<=120 else('mid'if m<=300 else'high'),frame_bits=768,seconds=time.monotonic()-t0)
  out.append(item)
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,m=m,q=q,r=r,scope='bounded representative same-q coordinate sanity, not fullgrid numerical T3',pair_selection='mandated ordinals'if forced_ordinals else'closest included equal-multiplicity pair near Omega or original selected cutoff',original_optimum_split_note='original zeta248 q127 includes only ordinal127; q128 is the distinct next sector including127/128'if m==248 and world=='zeta'and q==128 else None,rows=out)
 (OUT/f'hermite_{world}_m{m}_q{q}.json').write_text(json.dumps(result,indent=2)+'\n');print('HERMITE',world,m,q,[(x['theta'],x['status'],x['relative_delta_difference'],x['projector_difference'])for x in out],flush=True)
 return result
if __name__=='__main__':
 run('zeta',248,128,[127,128],283.2111857332339)
 old=base.original('zeta',310)['summary'];T=old['best_kappa']*float(2*G.const_pi()*310/G.log(310));run('zeta',310,old['best_q'],cutoff=T)
