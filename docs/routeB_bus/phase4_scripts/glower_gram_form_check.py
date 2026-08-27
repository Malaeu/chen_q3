"""P-M2 Мифоса: Грам-форма B_480 − d⁻¹·Σ_k r_k r_kᵀ вместо скаляра B_480 − p·I."""
import importlib.util, sys, time
from pathlib import Path
REPO = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("p1", REPO/"docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py")
p1 = importlib.util.module_from_spec(spec); sys.modules["p1"] = p1; spec.loader.exec_module(p1)
DPS, N, R, S = 200, 960, 70, 480
p1.ctx.dps = DPS; p1.N = N
from flint import arb, arb_mat
c0 = arb(1)/arb(10)**58; d = arb(1) - c0
t0=time.time(); b = p1.CCMArbBuilder(); _e, odd, _s = b.parity_blocks()
print(f"odd {odd.nrows()}² за {time.time()-t0:.0f}с", flush=True)

A = arb_mat(R,R); D = arb_mat(S-R,S-R); E = arb_mat(S-R,R)
for i in range(R):
    for j in range(R): A[i,j] = odd[i,j]
    A[i,i] = A[i,i] - c0
for i in range(S-R):
    for j in range(S-R): D[i,j] = odd[R+i,R+j]
    D[i,i] = D[i,i] - c0
    for j in range(R): E[i,j] = odd[R+i,j]
mE = arb_mat(S-R,R)
for i in range(S-R):
    for j in range(R): mE[i,j] = -E[i,j]
Y = D.solve(mE)

# B_480: Шур головы на замороженном разбиении
EtY = E.transpose()*Y
B = A + EtY + EtY.transpose() + Y.transpose()*D*Y
rep = p1.interval_ldlt(B)
print(f"B_480 сам по себе: {rep['status']}", flush=True)

# Грам невязок за S
t0=time.time(); G = arb_mat(R,R); tr = arb(0)
for k in range(S, odd.nrows()):
    r = [odd[k,j] for j in range(R)]
    for m in range(S-R):
        dkm = odd[k, R+m]
        for j in range(R): r[j] = r[j] + dkm*Y[m,j]
    for i in range(R):
        tr += r[i]*r[i]
        for j in range(i, R):
            v = r[i]*r[j]
            G[i,j] = G[i,j] + v
            if i != j: G[j,i] = G[j,i] + v
print(f"Грам собран за {time.time()-t0:.0f}с; след Σ‖r_k‖² = {float(tr.mid()):.6e}", flush=True)

cert = arb_mat(R,R)
inv_d = arb(1)/d
for i in range(R):
    for j in range(R): cert[i,j] = B[i,j] - inv_d*G[i,j]
rep2 = p1.interval_ldlt(cert)
print()
print(f"P-M2  B_480 − d⁻¹·Σ r_k r_kᵀ :  {rep2['status']}")
if rep2["pass"]:
    print(f"   мин.пивот {str(rep2['minimum_pivot']['lower'])[:30]}")
    print("GRAM_FORM=PASS_ON_PREFIX")
else:
    print(f"   провал на пивоте {rep2.get('failed_pivot_index')} из {R}")
    print(f"   пивот {rep2.get('failed_pivot',{}).get('ball')}")
    print("GRAM_FORM=FAIL_ON_PREFIX")
