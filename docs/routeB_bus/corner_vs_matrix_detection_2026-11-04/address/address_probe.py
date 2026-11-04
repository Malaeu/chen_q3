#!/usr/bin/env python3
"""Frozen DH selected-entry screen + zero-address diagnostics; no eigenproblems."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import ast,csv,hashlib,importlib.util,json,sys,time
from pathlib import Path
import numpy as np
from scipy.special import digamma
from scipy.stats import spearmanr,rankdata
from threadpoolctl import threadpool_limits
P=Path(__file__).resolve().parent;ROOT=P.parent
sys.path.insert(0,'/workspace/conditioning_deps')

def read(n):return json.loads((P/n).read_text())
def write(n,x):(P/n).write_text(json.dumps(x,indent=2)+'\n')
def csvout(n,rows):
 with (P/n).open('w',newline='')as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 t0=time.perf_counter(); receipt=json.loads((ROOT/'ADDRESS_PRE_RUN_RECEIPT.json').read_text());assert receipt['confirmed_remote_prediction_commit']==receipt['sha'];assert receipt['predictions_sha256']==sha(ROOT/'PREDICTIONS.md')
 source=ROOT/'inputs/analytic_source.py';assert sha(source)=='4e26ed90c8ef7305699802c02490bb0cea0da26be49891c98d387b5210eb8f63'
 spec=importlib.util.spec_from_file_location('_address_pinned',source);pinned=importlib.util.module_from_spec(spec);spec.loader.exec_module(pinned)
 coeff=pinned.coefficients(2000,256);Bz,Bd=[np.array([float(x)for x in b])for b in coeff]
 # Exact original function bodies; only return live intermediates additionally.
 # No DH formula or operation is rewritten. The original top-level import had
 # machine-specific paths and execution side effects; avoid both via AST load.
 src=P/'inputs/add_second_rung_raw.py';tree=ast.parse(src.read_text()); funcs=[n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name in ('trigamma','calc')]
 original_dh_ast=ast.dump(next(n for n in funcs if n.name=='calc'),include_attributes=False)
 fun=next(n for n in funcs if n.name=='calc');ret=fun.body[-1];assert isinstance(ret,ast.Return)
 ret.value=ast.Tuple(elts=[ret.value,ast.Call(func=ast.Name(id='locals',ctx=ast.Load()),args=[],keywords=[])],ctx=ast.Load())
 env=dict(np=np,digamma=digamma,B=Bd,BER=[1/6,-1/30,1/42,-1/30,5/66,-691/2730,7/6,-3617/510,43867/798,-174611/330,854513/138,-236364091/2730]);exec(compile(ast.fix_missing_locations(ast.Module(body=funcs,type_ignores=[])),str(src),'exec'),env)
 dhcalc=env['calc'];trigamma=env['trigamma']
 zeros=read('inputs/dh_zeros_900_200dps.json');assert len(zeros['off_line_pairs'])==26 and len(zeros['critical_line_zeros'])==746
 off=sorted(zeros['off_line_pairs'],key=lambda z:float(z['gamma']));on=sorted(zeros['critical_line_zeros'],key=lambda z:float(z['gamma']))
 og=np.array([float(z['gamma'])for z in off]);ob=np.array([float(z['sigma_right'])for z in off]);ng=np.array([float(z['gamma'])for z in on]);bound=float(zeros['height_bound'])
 saved={int(r['m']):r for r in csv.DictReader((P/'inputs/ADD_DH_DENSE.csv').open())}
 rng=np.random.default_rng(20261104);events=[];zcontrols=[];randomrows=[];gates=[];null_off=[];null_on=[];null_w=[];null_in=[]
 firsts=[dict(pair=k+1,beta=ob[k],displacement=ob[k]-.5,gamma=og[k],first_m=None,first_diagonal_m=None,first_minor_m=None,first_mode=None)for k in range(len(og))]
 def distances(w,step):
  w=np.asarray(w);oi=np.argmin(abs(w[:,None]-og[None,:]),axis=1);ni=np.argmin(abs(w[:,None]-ng[None,:]),axis=1)
  od=abs(w-og[oi])/step;nd=abs(w-ng[ni])/step
  return oi,ni,od,nd
 def zeta_diagonal(m,d):
  L=d['L'];j=d['j'];om=d['om'];om2=d['om2'];r=d['r'];sn=d['sn'];cs=d['cs']
  w=Bz[2:m]/np.sqrt(np.arange(2,m,dtype=float));sums=sn@w;pd=2*(cs@(w*(1-r)));pd[1:]-=sums[1:]/(np.pi*j[1:])
  z=.25+.5j*om;ps=digamma(z);tr=trigamma(z);a=.5+2*np.arange(256);ee=np.exp(-a*L);den=a[:,None]**2+om2[None,:]
  dg=ps.real-digamma(.25)+tr.real/(2*L);dg[1:]+=ps.imag[1:]/(L*om[1:]);dg-=np.sum(ee[:,None]*(2*om2[None,:]/(a[:,None]*den)+4*a[:,None]**2/(L*den**2)+2*a[:,None]/den),axis=0)
  dg[0]=float(trigamma(np.array([.25+0j]))[0].real)/(2*L)-2/L*np.sum(ee/a**2)-2*np.sum(ee/a)
  zz=np.exp(-L/2);pole=np.sqrt(2/L)*np.where(j==0,1,np.sqrt(2))*np.sinh(L/4)/(om2+.25)
  return -np.euler_gamma-np.log(8*np.pi)-np.pi/2+dg+2*(np.arctanh(zz)+np.arctan(zz))-pd+pole*pole
 with threadpool_limits(limits=1):
  for m in range(2,2001):
   (rec,rat,det,diag),d=dhcalc(m);s=saved[m];dn=int(np.sum(diag[1:]<0));mn=int(np.sum(det<0));assert dn==int(s['negative_Ajj_count'])and mn==int(s['negative_det_count']),(m,dn,mn,s)
   gates.append(dict(m=m,diag_count=dn,minor_count=mn,A00=rec['A00'],saved_A00=float(s['A00']),A00_difference=rec['A00']-float(s['A00']),min_Ajj=float(np.min(diag[1:])),saved_min_Ajj=float(s['min_Ajj']),min_det=float(np.min(det)),saved_min_det=float(s['min_det'])))
   js=np.where((diag[1:]<0)|(det<0))[0]+1
   if len(js):
    step=2*np.pi/np.log(m);omega=step*js;oi,ni,od,nd=distances(omega,step)
    for pos,j in enumerate(js):
     k=oi[pos];n=ni[pos];w=omega[pos]
     row=dict(m=m,j=int(j),omega=w,grid_step=step,Ajj=float(diag[j]),minor_det=float(det[j-1]),negative_diagonal=bool(diag[j]<0),failed_minor=bool(det[j-1]<0),off_pair=int(k+1),off_gamma=og[k],off_beta=ob[k],off_displacement=ob[k]-.5,off_distance_steps=od[pos],on_index=int(n+1),on_gamma=ng[n],on_distance_steps=nd[pos],within_census=bool(w<=bound),off_upper_census_ambiguous=bool(w+od[pos]*step>=bound),on_upper_census_ambiguous=bool(w+nd[pos]*step>=bound));events.append(row)
    for k,g in enumerate(og):
     hits=js[abs(omega-g)<=step]
     if len(hits):
      f=firsts[k]
      if f['first_m']is None:f.update(first_m=m,first_mode=int(hits[np.argmin(abs(step*hits-g))]),Omega=step*m)
      if f['first_diagonal_m']is None and np.any(diag[hits]<0):f['first_diagonal_m']=m
      if f['first_minor_m']is None and np.any(det[hits-1]<0):f['first_minor_m']=m
    zd=zeta_diagonal(m,d);zjs=np.argsort(zd,kind='stable')[:20];zo,zn,zod,znd=distances(zjs*step,step)
    for q,j in enumerate(zjs):zcontrols.append(dict(m=m,j=int(j),omega=j*step,zeta_diagonal=float(zd[j]),event_weight=len(js)/20,off_pair=int(zo[q]+1),off_distance_steps=zod[q],on_index=int(zn[q]+1),on_distance_steps=znd[q],within_census=bool(j*step<=bound)))
    rw=rng.uniform(0,step*m,1000);ro,rn,rod,rnd=distances(rw,step);weights=np.full(1000,len(js)/1000);null_off.extend(rod);null_on.extend(rnd);null_w.extend(weights);null_in.extend(rw<=bound)
    randomrows.append(dict(m=m,event_count=len(js),draws=1000,Omega=step*m,off_hit_fraction=float(np.mean(rod<=1)),on_hit_fraction=float(np.mean(rnd<=1)),off_median_steps=float(np.median(rod)),on_median_steps=float(np.median(rnd)),draws_within_census=int(np.sum(rw<=bound))))
   if m%100==0:print('ADDRESS',m,'events',len(events),'seconds',time.perf_counter()-t0,flush=True)
 # Standard-library witnesses keep source addresses and event identities stable.
 assert all(r['A00']>=0 for r in gates)
 csvout('events.csv',events);csvout('zeta_small_diagonal_controls.csv',zcontrols);csvout('uniform_control_by_m.csv',randomrows);csvout('dense_reconstruction_gate.csv',gates)
 for f in firsts:f['censored']=f['first_m']is None;f['threshold_report']='>2000'if f['censored']else str(f['first_m'])
 csvout('pair_first_detections.csv',firsts)
 def stats(od,nd,w=None,mask=None):
  od=np.asarray(od);nd=np.asarray(nd);w=np.ones(len(od))if w is None else np.asarray(w)
  if mask is not None:mask=np.asarray(mask);od=od[mask];nd=nd[mask];w=w[mask]
  def median(x):
   ix=np.argsort(x);return float(x[ix[np.searchsorted(np.cumsum(w[ix]),sum(w)/2)]])
  return dict(count=len(od),weight=float(sum(w)),off_within_one=float(np.average(od<=1,weights=w)),on_within_one=float(np.average(nd<=1,weights=w)),off_median_steps=median(od),on_median_steps=median(nd),off_closer_fraction=float(np.average(od<nd,weights=w)))
 def eventstats(rows,weights=None,mask=None):return stats([r['off_distance_steps']for r in rows],[r['on_distance_steps']for r in rows],weights,mask)
 es=eventstats(events);inside=eventstats(events,mask=[r['within_census']for r in events]);observed=[r for r in firsts if not r['censored']];beta=[r['beta']for r in observed];fm=[r['first_m']for r in observed]
 rho=spearmanr(beta,fm);allrho=spearmanr([r['beta']for r in firsts],[r['first_m'] or 2001 for r in firsts])
 partial=None
 if len(observed)>3:
  x=np.column_stack([np.ones(len(observed)),rankdata([r['gamma']for r in observed])]);rb=rankdata(beta);rf=rankdata(fm);eb=rb-x@np.linalg.lstsq(x,rb,rcond=None)[0];ef=rf-x@np.linalg.lstsq(x,rf,rcond=None)[0];partial=float(np.corrcoef(eb,ef)[0,1])
 def ad2(s):return s['off_within_one']>=s['on_within_one']and s['off_median_steps']<=s['on_median_steps']
 result=dict(honesty='DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER / NOT_RH; D0 unchanged',status='COMPLETE_ADDRESS_SCREEN',prediction_commit=receipt['sha'],seed=20261104,all_m=[2,2000],events=es,events_within_census=inside,
  diagonal_only_count=sum(r['negative_diagonal']and not r['failed_minor']for r in events),minor_only_count=sum(r['failed_minor']and not r['negative_diagonal']for r in events),both_count=sum(r['failed_minor']and r['negative_diagonal']for r in events),
  uniform_event_weighted=stats(null_off,null_on,null_w),uniform_event_weighted_within_census=stats(null_off,null_on,null_w,null_in),
  zeta_control_equal_m=eventstats(zcontrols),zeta_control_event_weighted=eventstats(zcontrols,[r['event_weight']for r in zcontrols]),zeta_control_event_weighted_within_census=eventstats(zcontrols,[r['event_weight']for r in zcontrols],[r['within_census']for r in zcontrols]),
  AD1=dict(pass_all=es['off_within_one']>=.9,pass_within_census=inside['off_within_one']>=.9),AD2=dict(pass_all=ad2(es),pass_within_census=ad2(inside)),AD3=dict(observed_pairs=len(observed),censored_pairs=len(firsts)-len(observed),Spearman_beta_first_m=float(rho.statistic),p_value_descriptive=float(rho.pvalue),pass_observed=bool(rho.statistic<0),censored_at_2001_rho=float(allrho.statistic),height_adjusted_partial_rank=partial),
  upper_census_ambiguous_events=sum(r['off_upper_census_ambiguous']or r['on_upper_census_ambiguous']for r in events),gate=dict(all1999_saved_diag_and_minor_counts_match=True,source_sha256=sha(source),frozen_selected_source_sha256=sha(src),original_dh_calc_ast_sha256=hashlib.sha256(original_dh_ast.encode()).hexdigest(),no_eigenproblems=True,interval_certificate=False),wall_seconds=time.perf_counter()-t0)
 write('SUMMARY.json',result)
 import matplotlib;matplotlib.use('Agg');import matplotlib.pyplot as plt
 fig,ax=plt.subplots(1,2,figsize=(10,4))
 for a,key,label in [(ax[0],'beta','off-line beta (right sigma)'),(ax[1],'gamma','off-line height gamma')]:
  a.scatter([r[key]for r in observed],[r['first_m']for r in observed],label='observed <=2000')
  cens=[r for r in firsts if r['censored']];a.scatter([r[key]for r in cens],[2001]*len(cens),marker='^',facecolors='none',edgecolors='red',label='censored >2000');a.set(xlabel=label,ylabel='first detected m');a.legend(fontsize=8)
 fig.suptitle('DH zero addresses: DIAGNOSTIC_NEVER_A_PROOF');fig.tight_layout();fig.savefig(P/'first_detection_by_beta_height.png',dpi=150);plt.close(fig)
 print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
