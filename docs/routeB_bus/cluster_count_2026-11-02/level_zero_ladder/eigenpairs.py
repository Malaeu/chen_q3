"""DIAGNOSTIC_NEVER_A_PROOF: full literal even-carrier eigenpairs."""
from pathlib import Path
import sys,json,time,hashlib
import mpmath as mp
OUT=Path(__file__).resolve().parent
BASE=OUT.parents[1]
sys.path.insert(0,str(BASE/'phase_space_V'))
from v_forms import build_forms
CONVENTION='e0=1/sqrt(L); en=sqrt(2/L)*(-1)^n*cos(2*pi*n*x/L), |x|<=L/2; zero outside'

def output(m,dps,order,A,V,ev,h,provenance,elapsed):
 mp.mp.dps=dps
 for i in range(m+1):
  pivot=max(range(m+1),key=lambda j:abs(V[j,i]))
  if (i==0 and mp.fdot(V[:,i],h)<0) or (i>0 and V[pivot,i]<0):V[:,i]=-V[:,i]
 fmt=lambda x:mp.nstr(x,dps)
 old=json.loads((OUT.parent/f'spectra_m{m}_dps100_gl128.json').read_text())
 data=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=m,N=m,L=fmt(mp.log(m)),dps=dps,order=order,basis=CONVENTION,sign_convention='ground positive theta overlap; other largest modal coordinate positive',lambda_=[fmt(x) for x in ev],A=[[fmt(x) for x in A[i,:]] for i in range(m+1)],V=[[fmt(x) for x in V[i,:]] for i in range(m+1)],h=[fmt(x) for x in h],eigen_residual=fmt(mp.norm(A*V-V*mp.diag(ev))),orthogonality_residual=fmt(mp.norm(V.T*V-mp.eye(m+1))),source_sha256=provenance,previous_count_spectrum_max_absolute_difference=fmt(max(abs(x-mp.mpf(y)) for x,y in zip(ev,old['lambda']))),previous_count_spectrum_relative_differences=[fmt(abs(x-mp.mpf(y))/abs(x)) for x,y in zip(ev,old['lambda'])],elapsed=elapsed)
 for B in (2,4,8):
  mu=mp.mpf(m)**(-B);data[f'count_B{B}']=sum(abs(x)<mu for x in ev);data[f'previous_count_B{B}']=sum(abs(mp.mpf(x))<mu for x in old['lambda'])
 p=OUT/f'cell_m{m}_dps{dps}_gl{order}.json';p.write_text(json.dumps(data,indent=2)+'\n');print(p.name,flush=True)

def main(m,dps,order):
 start=time.monotonic()
 if m in (16,24) and (dps,order)==(180,160):
  p=BASE/f'lowcluster_2026-11-02/ladder_limit/identify/zero_height_local/core_m{m}_dps180_gl160.json';d=json.loads(p.read_text());mp.mp.dps=dps
  A,V,ev,h=mp.matrix(d['A']),mp.matrix(d['V']),mp.matrix(d['lambda_']),mp.matrix(d['h']);provenance={str(p.relative_to(BASE)):hashlib.sha256(p.read_bytes()).hexdigest()}
 else:
  forms=build_forms(m,m,dps,order);A=forms['K'];h=forms['h'];ev,V=mp.eigsy(A);p=BASE/'phase_space_V/v_forms.py';provenance={str(p.relative_to(BASE)):hashlib.sha256(p.read_bytes()).hexdigest()}
 output(m,dps,order,A,V,ev,h,provenance,time.monotonic()-start)
def validate():
 mp.mp.dps=200
 a=json.loads((OUT/'cell_m40_dps160_gl128.json').read_text());b=json.loads((OUT/'cell_m40_dps180_gl160.json').read_text());U=mp.matrix(a['V']);V=mp.matrix(b['V'])
 data={'status':'DIAGNOSTIC_NEVER_A_PROOF','m':40,'source_files':['cell_m40_dps160_gl128.json','cell_m40_dps180_gl160.json'],'eigenvalue_relative_differences':[mp.nstr(abs(mp.mpf(x)-mp.mpf(y))/abs(mp.mpf(y)),90) for x,y in zip(a['lambda_'],b['lambda_'])],'eigenvector_L2_differences':[mp.nstr(mp.norm(U[:,i]-V[:,i]),90) for i in range(41)],'A_max_absolute_difference':mp.nstr(max(abs(x) for x in mp.matrix(a['A'])-mp.matrix(b['A'])),90),'all_threshold_counts_match':all(a[f'count_B{B}']==b[f'count_B{B}'] for B in (2,4,8))}
 (OUT/'cell_m40_validation.json').write_text(json.dumps(data,indent=2)+'\n')
 print('validation complete',flush=True)
if __name__=='__main__':
 if sys.argv[1]=='validate':validate()
 else:main(*map(int,sys.argv[1:]))
