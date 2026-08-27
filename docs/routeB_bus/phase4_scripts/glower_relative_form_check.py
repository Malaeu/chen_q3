"""Относительная форма: G ⪯ μ·B ?  То есть max eig(B^-1 G) против d = 1−c₀.

Если μ_max < d, то B − d⁻¹G ⪰ (1 − μ_max/d)·B ≻ 0 — сертификат проходит
в относительной форме там, где абсолютная (B − d⁻¹G с полным Грамом) падает.
Это в точности Re-representation 2 вердикта: ‖A₀^{-1/2} V A₀^{-1/2}‖ < 1.
"""
import importlib.util, sys, time
from pathlib import Path
REPO = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("p1", REPO/"docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py")
p1 = importlib.util.module_from_spec(spec); sys.modules["p1"]=p1; spec.loader.exec_module(p1)
DPS, N, R, S = 200, 960, 70, 480
p1.ctx.dps = DPS; p1.N = N
from flint import arb, arb_mat
from mpmath import mp, mpf, matrix as mpm, eigsy, cholesky, lu_solve
mp.dps = DPS
c0 = arb(1)/arb(10)**58; d = arb(1)-c0
t0=time.time(); b=p1.CCMArbBuilder(); _e,odd,_s=b.parity_blocks()
print(f"odd за {time.time()-t0:.0f}с", flush=True)
A=arb_mat(R,R); D=arb_mat(S-R,S-R); E=arb_mat(S-R,R)
for i in range(R):
    for j in range(R): A[i,j]=odd[i,j]
    A[i,i]=A[i,i]-c0
for i in range(S-R):
    for j in range(S-R): D[i,j]=odd[R+i,R+j]
    D[i,i]=D[i,i]-c0
    for j in range(R): E[i,j]=odd[R+i,j]
mE=arb_mat(S-R,R)
for i in range(S-R):
    for j in range(R): mE[i,j]=-E[i,j]
Y=D.solve(mE); EtY=E.transpose()*Y
B=A+EtY+EtY.transpose()+Y.transpose()*D*Y
G=arb_mat(R,R)
for k in range(S, odd.nrows()):
    r=[odd[k,j] for j in range(R)]
    for m_ in range(S-R):
        dkm=odd[k,R+m_]
        for j in range(R): r[j]=r[j]+dkm*Y[m_,j]
    for i in range(R):
        for j in range(i,R):
            v=r[i]*r[j]; G[i,j]=G[i,j]+v
            if i!=j: G[j,i]=G[j,i]+v
Bm=mpm(R,R); Gm=mpm(R,R)
for i in range(R):
    for j in range(R):
        Bm[i,j]=mpf(B[i,j].mid().str(DPS, radius=False))
        Gm[i,j]=mpf(G[i,j].mid().str(DPS, radius=False))
print("обобщённая задача G v = mu B v  →  eig(B^-1 G) …", flush=True)
t0=time.time()
Lc = cholesky(Bm)                      # B = L L^T, B ≻ 0 проверено ранее
# M = L^-1 G L^-T, симметричная
X = mpm(R,R)
for j in range(R):
    col = lu_solve(Lc, mpm([Gm[i,j] for i in range(R)]), )
    for i in range(R): X[i,j]=col[i]
M = mpm(R,R)
for i in range(R):
    row = lu_solve(Lc, mpm([X[i,j] for j in range(R)]))
    for j in range(R): M[i,j]=row[j]
for i in range(R):
    for j in range(i+1,R):
        avg=(M[i,j]+M[j,i])/2; M[i,j]=avg; M[j,i]=avg
mu = eigsy(M, eigvals_only=True)
mu_max = max(mu); mu_min = min(mu)
print(f"  за {time.time()-t0:.0f}с")
print()
print(f"  mu_max = {mp.nstr(mu_max, 10)}")
print(f"  mu_min = {mp.nstr(mu_min, 10)}")
print(f"  d      = 1 - c0 ≈ 1")
print()
if mu_max < 1:
    print(f"  G ⪯ {mp.nstr(mu_max,6)}·B  →  B − d⁻¹G ⪰ (1 − {mp.nstr(mu_max,6)})·B ≻ 0")
    print("RELATIVE_FORM=PASS")
else:
    print(f"  mu_max ≥ 1 → относительная форма НЕ проходит")
    print("RELATIVE_FORM=FAIL")
