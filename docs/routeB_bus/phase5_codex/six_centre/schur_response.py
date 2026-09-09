"""Schur response of the cut theta test on the window (Proshka DISTANCE D22-D24, request §9(c)): evaluate the signed
cancellation r vs b*C^{-1}b independently of the eigen routine. Input: window_derivative_K36_vec_matrices.npz (Q, G, cut-Phi
coefficients c per a). p = v_in/||v_in||_G; complement = G-orthogonal complement of p; r = Q[p]; b = Q(complement, p);
C = Q on complement. If C > 0: y = C^{-1} b, s0 = r - b* C^{-1} b, quotient s0/(1+||y||_G^2) (= lambda_1 iff the secular
equation D23 is solved at lambda_1; here it is the Rayleigh value of the Schur trial p - y, an UPPER bound for lambda_1).
Also the exact secular check D23: r - lambda_1 - b*(C - lambda_1)^{-1} b = 0.  DIAGNOSTIC_NEVER_A_PROOF."""
import numpy as np, scipy.linalg as sla, json, sys
z=np.load(sys.argv[1]); out={}
keys=sorted({k.rsplit('_',1)[0] for k in z.files}, key=float)
print(" a     r=Q[p]      b*C^-1 b     s0=r-b*C^-1b   ||y||^2_G   s0/(1+||y||^2)   lam1(eig)    minspec(C)   secular D23")
for a in keys:
    Q=z[f'{a}_Q']; G=z[f'{a}_G']; c=z[f'{a}_c']; ev=z[f'{a}_ev']; lam1=ev[0]
    # G-orthonormal basis: L L^T = G ; work in coordinates x = L^T v  =>  <v,w>_G = x.y ; Q -> L^{-1} Q L^{-T}
    L=np.linalg.cholesky(G); Li=np.linalg.inv(L); Qt=Li@Q@Li.T
    pt=L.T@c; pt=pt/np.linalg.norm(pt)
    # complement basis: Householder-complete pt to an orthonormal basis
    U,_=np.linalg.qr(np.column_stack([pt,np.eye(len(pt))]))  # first column = ±pt
    U=U[:,1:]  # orthonormal complement of pt
    r=float(pt@Qt@pt); b=U.T@Qt@pt; C=U.T@Qt@U
    cev=np.linalg.eigvalsh(C); minC=cev[0]
    y=np.linalg.solve(C,b); bCb=float(b@y); s0=r-bCb; ny=float(y@y); quot=s0/(1+ny)
    sec=r-lam1-float(b@np.linalg.solve(C-lam1*np.eye(len(b)),b))
    out[a]=dict(r=r,bCinvb=bCb,s0=s0,y2=ny,schur_quotient=quot,lam1=float(lam1),minspecC=float(minC),secular=sec,cancellation_ratio=bCb/r)
    print(f"{a}  {r:.4e}  {bCb:.4e}   {s0:.4e}    {ny:.4e}   {quot:.4e}     {lam1:.4e}   {minC:.4e}   {sec:.2e}")
json.dump(out,open(sys.argv[1].replace('_matrices.npz','_schur.json'),'w'),indent=1)
