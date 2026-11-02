"""Higher precision validation of one large passing capacity sector."""
from pathlib import Path
import sys,json,csv,time,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P.parent/'phase_space_V'));from v_forms import build_forms

def run(m,q):
 start=time.monotonic();mp.mp.dps=160;cache=P/f'large_validation_m{m}_q26.json'
 if q!=26 and cache.exists():
  previous=json.loads(cache.read_text());A=mp.matrix(previous['matrix_A']);L=mp.log(m);ev=mp.eigsy(A,eigvals_only=True);matrix_input_digits=150
 else:
  forms=build_forms(m,m,160,160);A=forms['K'];L=forms['L'];ev=mp.eigsy(A,eigvals_only=True);matrix_input_digits=160
 z=[mp.mpf(r['gamma']) for r in csv.DictReader((P.parent/'capacity_matrix_2026-11-02/zeros.csv').open())][:q]
 E=mp.matrix(q,m+1)
 for j,t in enumerate(z):
  for n in range(m+1):E[j,n]=2*(1 if n==0 else mp.sqrt(2))*t*mp.sin(t*L/2)/(mp.sqrt(L)*(t*t-(2*mp.pi*n/L)**2))
 U,S,V=mp.svd_r(E,full_matrices=True);Q=V[q:,:].T;r=m+1-q;X=A*Q;ae=mp.eigsy(X.T*X,eigvals_only=True);delta=mp.sqrt(ae[ae.rows-1]);sigma=S[q-1];lam=ev[r]
 fmt=lambda v:mp.nstr(v,150)
 result=dict(m=m,q=q,r=r,dps=160,order=160,matrix_input_digits=matrix_input_digits,delta=fmt(delta),lambda_r=fmt(lam),lambda_r_minus_delta=fmt(lam-delta),sigma_min_squared=fmt(sigma*sigma),twice_sigma_min_squared=fmt(2*sigma*sigma),count_abs_lambda_le_delta=sum(abs(x)<=delta for x in ev),kernel_residual=fmt(mp.norm(E*Q)),orthogonality_residual=fmt(mp.norm(Q.T*Q-mp.eye(r))),svd_reconstruction_residual=fmt(mp.norm(E-U*mp.diag(S)*V[:q,:])),weak_left_vector=[fmt(x) for x in U[:,q-1]],matrix_A=[[fmt(x) for x in A[i,:]] for i in range(m+1)],eigenvalues=[fmt(x) for x in ev],source_sha256=hashlib.sha256((P.parent/'phase_space_V/v_forms.py').read_bytes()).hexdigest(),seconds=time.monotonic()-start)
 (P/f'large_validation_m{m}_q{q}.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k not in ['matrix_A','weak_left_vector','eigenvalues']},flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
