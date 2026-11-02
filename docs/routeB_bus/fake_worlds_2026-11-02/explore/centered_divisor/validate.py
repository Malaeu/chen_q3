"""High precision comparison and independent output-space centered-norm checks."""
from pathlib import Path
from fractions import Fraction
from math import gcd
import json,gzip,sys
import mpmath as mp
from centered import matrix_from_mom,atom_moments,mangoldt,P,FAKE
mp.mp.dps=180
main=json.loads((P/'cell_m120_dps100.json').read_text());high=json.loads((P/'cell_m120_dps160.json').read_text());out={}
for key in ['centered_matrix','raw_matrix','continuum_matrix']:
 X=mp.matrix(main[key])-mp.matrix(high[key]);out[key+'_max_entry_difference']=mp.nstr(max(abs(x) for x in X),100);out[key+'_Frobenius_difference']=mp.nstr(mp.norm(X),100)
for key in ['centered_complement_max','q_complement_operator_norm','ratio','ratio_over_L','centered_full_min']:
 out[key+'_relative_difference']=mp.nstr(abs(mp.mpf(main[key])/mp.mpf(high[key])-1),100)
f=mp.matrix(main['top_physical_vector']);g=mp.matrix(high['top_physical_vector']);out['top_vector_difference_up_to_sign']=mp.nstr(min(mp.norm(f-g),mp.norm(f+g)),100);out['peak_height_absolute_difference']=mp.nstr(abs(mp.mpf(main['peak']['t'])-mp.mpf(high['peak']['t'])),100)
# Direct per-entry higher-power Q construction, then singular-value operator norm.
m=120;L=mp.log(m);source=json.loads((FAKE/'ledger_diff/matched_cells/zeta_m120_q64.json').read_text());A=mp.matrix(source['A']);U=mp.matrix(source['U']);q=A+(mp.euler+mp.log(8*mp.pi)+mp.pi/2-4)*mp.eye(m+1);ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
for n in [8,16,27,32,64,81]:
 s=mp.log(n);weight=mangoldt(n)/mp.sqrt(n);si=[mp.sin(2*mp.pi*i*s/L) for i in range(m+1)];co=[mp.cos(2*mp.pi*i*s/L) for i in range(m+1)]
 for i in range(m+1):
  q[i,i]+=weight*(2*(1-s/L)*co[i]-(si[i]/(mp.pi*i) if i else 0))
  for k in range(i+1,m+1):
   v=weight*ds[i]*ds[k]/mp.pi*(k*si[k]-i*si[i])/(i*i-k*k);q[i,k]+=v;q[k,i]+=v
svals=mp.svd_r(U.T*q*U,compute_uv=False);out['q_denominator_independent_SVD']=mp.nstr(svals[0],150);out['q_denominator_SVD_relative_difference']=mp.nstr(abs(svals[0]/mp.mpf(high['q_complement_operator_norm'])-1),100)
# Independent small-m physical output integral, including the untruncated tail.
mp.mp.dps=80;m=6;L=mp.log(m);b=L/2;N=3;v=mp.matrix([mp.mpf(2)/3,-mp.mpf(1)/5,0,mp.mpf(1)/7]);v/=mp.norm(v);om=2*mp.pi/L;ds=[1,mp.sqrt(2),mp.sqrt(2),mp.sqrt(2)]
def fun(x):return mp.fsum(v[n]*ds[n]*(-1)**n*mp.cos(n*om*x)/mp.sqrt(L) for n in range(4))
def primitive(x):return mp.fsum(v[n]*ds[n]*(-1)**n/mp.sqrt(L)*mp.exp(x/2)*(mp.cos(n*om*x)/2+n*om*mp.sin(n*om*x))/(mp.mpf('.25')+(n*om)**2) for n in range(4))
base=primitive(-b);whole=primitive(b)-base
norms={}
for NN in [1,2,3]:
 def C(x):
  upper=min(b,x+mp.log(NN))
  return 0 if upper<=-b else mp.exp(-x/2)*(primitive(upper)-base)
 def Z(x):return mp.fsum(fun(x+mp.log(k))/mp.sqrt(k) for k in range(1,NN+1) if -b<=x+mp.log(k)<=b)
 points=sorted(set([-b-mp.log(k) for k in range(1,NN+1)]+[b-mp.log(k) for k in range(1,NN+1)]));body=mp.fsum(mp.quad(lambda x:(Z(x)-C(x))**2,[a,c]) for a,c in zip(points,points[1:]));tail=whole**2*mp.exp(-b);norms[NN]=body+tail
h=[mp.mpf(0)]
for j in range(1,m+1):h.append(h[-1]+mp.log(j)/j)
atoms=[(mp.log(mp.mpf(a)/bb),h[m//a]/mp.sqrt(a*bb)) for a in range(2,m+1) for bb in range(1,a) if gcd(a,bb)==1 and h[m//a]]
raw=matrix_from_mom(*atom_moments(3,L,atoms),L)+h[m]*mp.eye(4);C=[mp.mpf(0)]*4;SC=C.copy();S=C.copy()
for d in range(2,m+1):
 if not mangoldt(d):continue
 NN=m//d
 for k in range(1,NN):
  upper=mp.log(mp.mpf(NN)/k);weight=mangoldt(d)/d
  for n in range(4):
   z=mp.mpf('.5')+mp.j*n*om;e=mp.exp(z*upper);i0=(e-1)/z;i1=(e*(z*upper-1)+1)/z**2;C[n]+=weight*mp.re(i0);SC[n]+=weight*mp.re(i1);S[n]+=weight*mp.im(i0)
moment=mp.fdot(v,(raw-matrix_from_mom(C,SC,S,L))*v);physical=mp.fsum(mangoldt(d)/d*norms[m//d] for d in range(2,m+1) if mangoldt(d))
out['small_physical_check']=dict(m=6,carrier_modes=3,dps=80,centered_moment_value=mp.nstr(moment,80),full_output_integral_value=mp.nstr(physical,80),absolute_difference=mp.nstr(abs(moment-physical),60),N1_norm=mp.nstr(norms[1],80),N1_identity_error=mp.nstr(abs(norms[1]-1),60),output_tail_in_each_N_norm=mp.nstr(whole**2*mp.exp(-b),80))
out['scope']='100 versus160 work precision on fixed120-digit source A,U; independent small physical output integration includes the tail; no interval certificate.'
(P/'validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
# Dense arrays stay available locally, but are not needed in publication cells.
for path in P.glob('cell_m*_dps*.json'):
 data=json.loads(path.read_text());dense={key:data.pop(key) for key in ['centered_matrix','raw_matrix','continuum_matrix'] if key in data}
 if dense:
  with gzip.open('/tmp/centered_divisor_dense_'+path.stem+'.json.gz','wt') as archive:json.dump(dense,archive)
 data['dense_arrays_publication']='omitted; reproducible with centered.py m dps 1';path.write_text(json.dumps(data,indent=2)+'\n')
