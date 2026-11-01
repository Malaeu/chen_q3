import sys,json
from pathlib import Path
import mpmath as mp
import probe as p
sys.path.insert(0,str(p.OUT.parents[1]/'fokas_k_sign_2026-09-25'))
import full_center_probe as fc
out=[]
for m in (8,16):
 L=mp.log(m);K,D=p.matrices(L,m,'right',m)
 src=fc.matrix_K(m)
 err=max(abs(K[i,j]-src[i,j]) for i in range(K.rows) for j in range(K.cols))
 r={'m':m,'max_entry_error_vs_source':p.fmt(err),'order':p.ORDER,'eigenvalues':{}}
 for N in (8,12,m):
  if N<=m:r['eigenvalues'][str(N)]=p.fmt(p.eig(K,N,m))
 out.append(r);print(json.dumps(r),flush=True)
for k in range(8,17):
 L=mp.log(k);N=12
 K,A=p.matrices(L,N,'left',k);K,B=p.matrices(L,N,'right',k)
 lam,v,gap=p.eig(K,N,N,True)
 E=mp.zeros(2*N+1,N+1);E[N,0]=1
 for n in range(1,N+1):E[N+n,n]=E[N-n,n]=1/mp.sqrt(2)
 f=E*v
 expected=-2*p.mang(k)/(L*mp.sqrt(k))*mp.fsum(f)**2
 measured=(v.T*p.even(B-A,N,N)*v)[0]
 r={'k':k,'N':N,'HF_jump':p.fmt(measured),'expected_rank_one_jump':p.fmt(expected),'jump_abs_difference':p.fmt(abs(measured-expected))}
 out.append(r);print(json.dumps(r),flush=True)
(p.OUT/f'validation_gl{p.ORDER}.json').write_text(json.dumps(out,indent=2)+'\n')
