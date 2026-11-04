"""Own-DH scalar checkpoint/coeff tests at60dps, no zeta source pieces."""
from pathlib import Path
from functools import lru_cache
import csv,json,math,struct,hashlib
import mpmath as mp
P=Path(__file__).resolve().parents[1];mp.mp.dps=60
T=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
def a(n):return [mp.mpf(0),mp.mpf(1),T,-T,mp.mpf(-1)][n%5]
@lru_cache(None)
def coeff(n):
 if n==1:return mp.mpf(0)
 ds=set()
 for k in range(1,math.isqrt(n)+1):
  if n%k==0:ds.add(k);ds.add(n//k)
 return a(n)*mp.log(n)-mp.fsum(coeff(d)*a(n//d)for d in ds if 1<d<n)
def psi(m,s1,s2):
 L=mp.log(m);return L*(mp.digamma(mp.mpf(3)/4)+mp.log(5/mp.pi))/2+(mp.zeta(2,mp.mpf(3)/4)-mp.exp(-3*L/2)*mp.lerchphi(mp.exp(-2*L),2,mp.mpf(3)/4))/4-L*s1+s2

def main():
 rows=[]
 for r in csv.DictReader((P/'ADD_DH_CHECKPOINT_SUMS.csv').open()):
  m=int(r['m']);s1=mp.mpf(r['S1_mp192']);s2=mp.mpf(r['S2_mp192']);v=psi(m,s1,s2);diff=v-mp.mpf(r['Psi_native'])
  rows.append(dict(kind=r['kind'],m=m,Psi_mp60=mp.nstr(v,62),Psi_native=r['Psi_native'],difference=mp.nstr(diff,62),S1_source_bits=192,S2_source_bits=192,scope='MPFR192 own-source sums with independent60dps Gamma/Lerch formula; point diagnostic'))
 spots=[]
 for r in csv.DictReader((P/'ADD_DH_COEFFICIENT_SPOTS.csv').open()):
  n=int(r['n']);exact=coeff(n);diff=mp.mpf(r['b_mp192'])-exact;assert abs(diff)<mp.mpf('1e-45')*max(1,abs(exact))
  spots.append(dict(n=n,b_recursion_mp60=mp.nstr(exact,62),b_convolution_mp192=r['b_mp192'],difference=mp.nstr(diff,62)))
 # Extra high-index nonzero/composite tests of independently recursive coefficients.
 raw=Path('/workspace/corner_thermometer/addendum/DH_coeff_n2_N.float64');extras=[]
 for n in [8388608,4782969,8957952,4064256,3592512,9999991,9356256]:
  exact=coeff(n)
  with raw.open('rb')as f:f.seek((n-2)*8);stored=struct.unpack('<d',f.read(8))[0]
  err=abs(mp.mpf(stored)-exact);assert err<mp.mpf('1e-12')*max(1,abs(exact))
  extras.append(dict(n=n,recursive_mp60=mp.nstr(exact,62),stored_binary64=stored,relative_scaled_error=mp.nstr(err/max(1,abs(exact)),20)))
 # Validate source corners against the independent row/diagonal engine on its grid.
 d=json.loads((P/'ADD_SECOND_RUNG.json').read_text());cross=[]
 for x in d['summary']:
  if x['world']!='dh':continue
  m=x['m'];ref=next(r for r in rows if r['m']==m);A00=mp.mpf(x['max_positive_denominator_ratio']['A00']);target=2*mp.mpf(ref['Psi_mp60'])/mp.log(m);diff=A00-target
  assert abs(diff)<mp.mpf('1e-45');cross.append(dict(m=m,row_A00=mp.nstr(A00,62),corner_A00=mp.nstr(target,62),difference=mp.nstr(diff,62)))
 # Genuine direct small-source construction at75 and463, independent of full-prefix sums.
 direct=[]
 for m in [75,463]:
  terms=[coeff(n)/mp.sqrt(n)for n in range(2,m)];s1=mp.fsum(terms);s2=mp.fsum(w*mp.log(n)for n,w in zip(range(2,m),terms));v=psi(m,s1,s2)
  direct.append(dict(m=m,Psi_direct60=mp.nstr(v,62),A00_direct60=mp.nstr(2*v/mp.log(m),62)))
 minimum=next(r for r in rows if r['kind']=='minimum');m=minimum['m'];ss=next(r for r in csv.DictReader((P/'ADD_DH_CHECKPOINT_SUMS.csv').open())if r['kind']=='minimum');s1=mp.mpf(ss['S1_mp192']);s2=mp.mpf(ss['S2_mp192']);near=[]
 for n in [m-1,m,m+1]:
  if n==m-1:w=coeff(n)/mp.sqrt(n);u1=s1-w;u2=s2-w*mp.log(n)
  elif n==m:u1,u2=s1,s2
  else:w=coeff(m)/mp.sqrt(m);u1=s1+w;u2=s2+w*mp.log(m)
  near.append(dict(m=n,Psi_mp60=mp.nstr(psi(n,u1,u2),62)))
 result=dict(status='DH_OWN_SOURCE_POINT_CHECKS_NOT_INTERVAL',formula='-c_D L/2 + [zeta(2,3/4)-e^(-3L/2)Phi(e^(-2L),2,3/4)]/4 - L S1+S2; no pole',dps=60,coefficient_bits=192,rows=rows,max_native_difference=mp.nstr(max(abs(mp.mpf(r['difference']))for r in rows),62),coefficient_spots=spots,large_coefficient_spots=extras,grid_crosscheck=cross,direct_small_corners=direct,minimum_neighborhood=near,minimum_neighborhood_winner=min(near,key=lambda r:mp.mpf(r['Psi_mp60'])))
 (P/'ADD_DH_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(max_native_difference=result['max_native_difference'],min=minimum,near=near,direct=direct),indent=2))
if __name__=='__main__':main()
