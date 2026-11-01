"""Finite limiting-ladder identification canary; DIAGNOSTIC_NEVER_A_PROOF.
Physical zero-extended transforms, accurate zeta zeros, explicit finite poles.
"""
from pathlib import Path
import json,csv,sys
import mpmath as mp
mp.mp.dps=140
OUT=Path(__file__).resolve().parent;LL=OUT.parent;ROOT=LL.parent
NAMES=[f'phi{i}' for i in range(8)]+['least_ladder']

def fmt(x):return mp.nstr(x,100)
def csvout(name,rows):
 with (OUT/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def H(t):
 s=mp.mpf('.5')-mp.j*t
 return mp.re(2*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s))
def load(m,high=False):
 name=f'core_m{m}_dps140_gl160.json' if high else f'core_m{m}_dps100_gl128.json'
 r=json.loads((ROOT/name).read_text());V=mp.matrix(r['V']);C=V[:,:8]
 if high:
  sys.path.insert(0,str(LL));from shape import extract_shape
  q=extract_shape(r)['coef']
 else:q=mp.matrix(next(x for x in json.loads((LL/'shape_results.json').read_text()) if x['summary']['m']==m)['physical_modal_coefficients'])
 A=mp.matrix(m+1,9)
 for i in range(m+1):
  for j in range(8):A[i,j]=C[i,j]
  A[i,8]=q[i]
 L=mp.log(m);om=[2*mp.pi*n/L for n in range(m+1)];ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
 return dict(m=m,L=L,b=L/2,C=A,omega=om,d=ds)

def sp(x):return (x*mp.cos(x)-mp.sin(x))/(x*x) if x else mp.mpf(0)
def transform_basis(a,t,derivative=False):
 L=a['L'];b=a['b'];out=[];ss=mp.sin(b*t);cc=mp.cos(b*t)
 for n,om in enumerate(a['omega']):
  if abs(t-om)<mp.mpf('1e-40') or abs(t+om)<mp.mpf('1e-40'):
   v=a['d'][n]*(-1)**n/mp.sqrt(L)*b*((b*sp((t-om)*b)+b*sp((t+om)*b)) if derivative else (mp.sinc((t-om)*b)+mp.sinc((t+om)*b)))
  else:
   den=t*t-om*om
   v=2*a['d'][n]/mp.sqrt(L)*((ss+b*t*cc)/den-2*t*t*ss/(den*den) if derivative else t*ss/den)
  out.append(v)
 return mp.matrix(out)
def evalall(a,t,derivative=False):return a['C'].T*transform_basis(a,t,derivative)
def evalone(a,j,t,derivative=False):return (a['C'][:,j].T*transform_basis(a,t,derivative))[0]
def cheb(y,d):
 v=[mp.mpf(1)]
 if d:v.append(y)
 for k in range(2,d+1):v.append(2*y*v[-1]-v[-2])
 return v

def main():
 zeros=[mp.im(mp.zetazero(k)) for k in range(1,11)];der=[mp.diff(H,g) for g in zeros]
 csvout('zeta_zeros.csv',[dict(k=k+1,gamma=fmt(g),H_at_gamma=fmt(H(g)),H_prime_at_gamma=fmt(der[k])) for k,g in enumerate(zeros)])
 data={m:load(m) for m in (20,24)};datahigh=load(24,True)
 ts=[mp.mpf(i)/20 for i in range(1601)]
 grids={};maxima={};maxrows=[]
 for m,a in data.items():
  grid=[evalall(a,t) for t in ts];grids[m]=grid;maxima[m]=[]
  for j in range(9):
   candidates=[mp.mpf(0),mp.mpf(80)]
   for i in range(1,len(ts)-1):
    if abs(grid[i][j])>=abs(grid[i-1][j]) and abs(grid[i][j])>=abs(grid[i+1][j]):
     z=mp.findroot(lambda t:evalone(a,j,t,True),(ts[i-1],ts[i+1]),tol=mp.mpf('1e-110'),maxsteps=40)
     if 0<=z<=80:candidates.append(z)
   tt=max(candidates,key=lambda t:abs(evalone(a,j,t)));v=abs(evalone(a,j,tt));maxima[m].append(v)
   # Bound all |t|>80 by the finite sinc representation.
   asum=mp.fsum(abs(a['C'][n,j])*a['d'][n]/mp.sqrt(a['L']) for n in range(m+1));tail=2*asum/(80-a['omega'][-1])
   assert tail<v,(m,j,tail,v)
   maxrows.append(dict(m=m,profile=NAMES[j],max_transform=fmt(v),argmax_abs_t=fmt(tt),search_step='0.05',search_T='80',stationary_candidates=len(candidates),tail_upper_bound_outside_T=fmt(tail),outside_search_cannot_exceed_found_peak=True))
  print('maxima done',m,flush=True)
 csvout('fourier_maxima.csv',maxrows)
 zero_rows=[];zero_values={}
 for m,a in data.items():
  vals=[evalall(a,g) for g in zeros];zero_values[m]=vals
  for j in range(9):
   for k,g in enumerate(zeros):
    v=vals[k][j];hi=evalone(datahigh,j,g) if m==24 else None
    zero_rows.append(dict(m=m,profile=NAMES[j],zero_index=k+1,gamma=fmt(g),fourier_value=fmt(v),absolute_normalized_residual=fmt(abs(v)/maxima[m][j]),ratio_pole_residue=fmt(v/der[k]),source140_value=fmt(hi) if hi is not None else '',relative_source_precision_change=fmt(abs((v-hi)/hi)) if hi is not None and hi else ''))
 csvout('radical_test.csv',zero_rows)
 trends=[]
 for j in range(9):
  for k in range(10):
   a=abs(zero_values[20][k][j])/maxima[20][j];b=abs(zero_values[24][k][j])/maxima[24][j]
   trends.append(dict(profile=NAMES[j],zero_index=k+1,residual_m20=fmt(a),residual_m24=fmt(b),m24_over_m20=fmt(b/a)))
 csvout('radical_trend.csv',trends)
 # Ratios on the ordinary grid. Zeros themselves are evaluated separately.
 ht=[H(t) for t in ts[:801]];ratio_rows=[]
 for m in (20,24):
  for it,t in enumerate(ts[:801]):
   r=dict(m=m,t=fmt(t),H=fmt(ht[it]),nearest_zero_distance=fmt(min(abs(t-g) for g in zeros)))
   for j in range(9):r[NAMES[j]]=fmt(grids[m][it][j]/ht[it])
   ratio_rows.append(r)
 csvout('ratios_grid.csv',ratio_rows)
 poles=[]
 for k,g in enumerate(zeros[:6]):
  for exponent in (2,6,12,24,40,60,80):
   delta=mp.power(10,-exponent)
   for sign in (-1,1):
    t=g+sign*delta;hh=H(t)
    for m,a in data.items():
     vv=evalall(a,t)
     for j in range(9):
      R=zero_values[m][k][j]/der[k];ratio=vv[j]/hh
      poles.append(dict(m=m,profile=NAMES[j],zero_index=k+1,delta_exponent=exponent,side=sign,ratio=fmt(ratio),delta_times_ratio=fmt(sign*delta*ratio),predicted_residue=fmt(R),scaled_residue_relative_error=fmt(abs((sign*delta*ratio-R)/R))))
 csvout('ratio_pole_checks.csv',poles)
 # Even-polynomial model Phi(t)=H(t) P(t²); fit transforms, not pole values.
 train=[i for i in range(0,801,2)]
 test=[i for i in range(1,800,2)]
 AA=mp.matrix([[ht[i]*z for z in cheb(2*(ts[i]/40)**2-1,15)] for i in train]);G=AA.T*AA
 YY=mp.matrix([[grids[m][i][j] for m in (20,24) for j in range(9)] for i in train]);rhs=AA.T*YY
 fitrows=[];coefrows=[]
 for d in (0,1,2,3,4,5,6,7,10,15):
  GG=G[:d+1,:d+1];ev=mp.eigsy(GG,eigvals_only=True);cond=ev[len(ev)-1]/ev[0];coef=mp.inverse(GG)*rhs[:d+1,:]
  for col in range(18):
   m=(20,24)[col//9];j=col%9;errors=[];rerrors=[];rmax=[]
   for i in test:
    pp=mp.fsum(coef[k,col]*z for k,z in enumerate(cheb(2*(ts[i]/40)**2-1,d)))
    errors.append(abs(grids[m][i][j]-ht[i]*pp)/maxima[m][j])
    if min(abs(ts[i]-g) for g in zeros[:6])>mp.mpf('.05'):
     rr=grids[m][i][j]/ht[i];rerrors.append(abs(rr-pp));rmax.append(abs(rr))
   fitrows.append(dict(m=m,profile=NAMES[j],polynomial_degree_in_t=2*d,fit='least squares Phi=H*P(t^2), training step0.1; holdout step0.1 shifted0.05',max_normalized_transform_holdout_error=fmt(max(errors)),relative_sup_quotient_holdout_error_away_0p05_from_zeros=fmt(max(rerrors)/max(rmax)),normal_matrix_condition=fmt(cond)))
   if d in (7,10,15):
    for k in range(d+1):coefrows.append(dict(m=m,profile=NAMES[j],degree_in_t=2*d,chebyshev_index=k,coefficient=fmt(coef[k,col]),variable='y=2*(t/40)^2-1'))
  print('fit degree',2*d,flush=True)
 csvout('polynomial_fits.csv',fitrows);csvout('polynomial_coefficients.csv',coefrows)
 summary=[]
 for m in (20,24):
  for j in range(9):
   ratios=[abs(zero_values[m][k][j])/maxima[m][j] for k in range(10)]
   summary.append(dict(m=m,profile=NAMES[j],max_normalized_zero_residual=fmt(max(ratios)),worst_zero_index=ratios.index(max(ratios))+1,min_normalized_zero_residual=fmt(min(ratios)),maximum_transform=fmt(maxima[m][j])))
 csvout('radical_summary.csv',summary)
 (OUT/'identification.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',dps=140,source_commit='d6e76475b98dcfe58fe649bcb22d3c126951279c',summary=summary,maxima=maxrows,zeros=[fmt(g) for g in zeros]),indent=2)+'\n')
 print('DONE',flush=True)
if __name__=='__main__':main()
