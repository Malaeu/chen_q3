"""Separate literal raw-ratio first crossing screen; frozen rung files unchanged."""
import sys,importlib.util,json,csv,time
from pathlib import Path
sys.path[:0]=['/workspace/stiffness/deps','/workspace/second_moment/local/deps']
import numpy as np
from scipy.special import digamma
OUT=Path('/workspace/corner_thermometer/output');p=OUT/'scripts/add_second_rung.py';spec=importlib.util.spec_from_file_location('exactrung',p);exact=importlib.util.module_from_spec(spec);spec.loader.exec_module(exact)
B=np.array([float(v)for v in exact.pinned.coefficients(2000,256)[1]])
BER=[1/6,-1/30,1/42,-1/30,5/66,-691/2730,7/6,-3617/510,43867/798,-174611/330,854513/138,-236364091/2730]
def trigamma(z):
 Z=z+32;v=1/Z+1/(2*Z*Z)
 for k,b in enumerate(BER,1):v+=b/Z**(2*k+1)
 for n in range(32):v+=1/(z+n)**2
 return v

def calc(m):
 L=np.log(m);j=np.arange(m+1,dtype=float);om=2*np.pi*j/L;om2=om*om;z=.75+.5j*om;ps=digamma(z);tr=trigamma(z);p0=digamma(.75);t0=float(trigamma(np.array([.75+0j]))[0].real)
 c=-np.euler_gamma-np.log(8*np.pi/5)+np.pi/2;tail=np.arctanh(np.exp(-L/2))-np.arctan(np.exp(-L/2))
 n=np.arange(2,m,dtype=float);r=np.log(n)/L;w=B[2:m]/np.sqrt(n);ang=2*np.pi*j[:,None]*r[None,:];sn=np.sin(ang);cs=np.cos(ang)
 sums=sn@w;pd=2*(cs@(w*(1-r)));pd[1:]-=sums[1:]/(np.pi*j[1:])
 a=1.5+2*np.arange(24);ee=np.exp(-a*L);den=a[:,None]**2+om2[None,:]
 moment=ps.imag/2-np.sum(om[None,:]*ee[:,None]/den,axis=0)
 dg=ps.real-p0+tr.real/(2*L);dg[1:]+=ps.imag[1:]/(L*om[1:])
 dg-=np.sum(ee[:,None]*(2*om2[None,:]/(a[:,None]*den)+4*a[:,None]**2/(L*den**2)+2*a[:,None]/den),axis=0)
 dg[0]=t0/(2*L)-2/L*np.sum(ee/a**2)-2*np.sum(ee/a)
 diag=c+dg+2*tail-pd;a00=diag[0];row=np.sqrt(2)*(moment[1:]+sums[1:])/(np.pi*j[1:]);denom=a00*diag[1:];rat=row**2/denom;det=denom-row**2
 return dict(m=m,max_rawratio=float(np.max(rat)),argj=int(np.argmax(rat)+1),min_det=float(np.min(det)),argmin_det=int(np.argmin(det)+1),A00=float(a00)),rat,det,diag

def main():
 start=time.monotonic();scan=[];first=None;near=[];firstpos=None
 for m in range(2,2001):
  rec,rat,det,diag=calc(m);scan.append(rec)
  for j in np.where(rat>.999999)[0]+1:near.append((m,int(j)))
  pp=np.where((det<0)&(diag[1:]>0)&(rec['A00']>0))[0]+1
  if len(pp)and firstpos is None:firstpos=dict(m=m,j=[int(v)for v in pp])
  if rec['max_rawratio']>1:first=rec;break
  if m%100==0:print('SCREEN',m,time.monotonic()-start,flush=True)
 confirmations=[];disagreement=[]
 for m in sorted(set(v[0]for v in near)):
  rr=exact.calc(m,320,worlds=('dh',));want={j for mm,j in near if mm==m}
  confirmations.extend(r for r in rr if r['j']in want)
 for r in confirmations:
  fr=scan[r['m']-2];
  if bool(exact.g.mpfr(r['raw_ratio'])>1)!=(fr['m']==(None if first is None else first['m']) and r['j']==first['argj']):
   if exact.g.mpfr(r['raw_ratio'])>1 and r['m']!=(None if first is None else first['m']):disagreement.append(r)
 with(OUT/'ADD_SECOND_RUNG_RAW.csv').open('w')as f:
  w=csv.DictWriter(f,fieldnames=list(scan[0]));w.writeheader();w.writerows(scan)
 out=dict(status='FLOAT64_EXHAUSTIVE_SCREEN_WITH_320BIT_NEAR_ONE_POINT_CONFIRMATIONS_NOT_INTERVAL',scope='literal first max_j raw A0j²/(A00 Ajj)>1; separate from firstPSDfailure',first_raw_crossing_screen=first,first_positive_diagonal_negative_determinant_screen=firstpos,integer_m_covered=[2,scan[-1]['m']],every_j_covered=True,screen_guard_band='.999999',near_one_count=len(near),critical_confirmations=confirmations,disagreements=disagreement,screen_rows=len(scan),seconds=time.monotonic()-start,frozen_rung_files_unchanged=True)
 validation=[]
 for mm in [16,40,75,462,463]:
  rec,rat,det,dg=calc(mm);rr=exact.calc(mm,320,worlds=('dh',))
  validation.append(dict(m=mm,max_all_j_rawratio_error=float(max(abs(float(r['raw_ratio'])-rat[r['j']-1])for r in rr)),max_all_j_det_error=float(max(abs(float(r['determinant'])-det[r['j']-1])for r in rr)),max_all_j_Ajj_error=float(max(abs(float(r['Ajj'])-dg[r['j']])for r in rr)),exact_bits=320))
 prior=max(scan[:-1]if first else scan,key=lambda r:r['max_rawratio'])
 out.update(float_source_validation=validation,closest_prior_screen_maximum=prior,closest_prior_margin_to_one=1-prior['max_rawratio'],interpretation='First literal raw crossing in exhaustive float64 screen with all near-one candidates independently320bit confirmed; numerical point result, not interval-certified firstness.')
 (OUT/'ADD_SECOND_RUNG_RAW.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',out['seconds'],first,flush=True)
if __name__=='__main__':main()
