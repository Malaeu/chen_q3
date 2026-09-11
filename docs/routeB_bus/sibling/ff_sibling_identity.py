"""Exact identity for the function-field sibling of SL12a/SL14 (observer, 2026-09-11, verified genus 1-3 to 1e-16).

    V(x,y) := Σ_{t≥0} (x+y+2t) φ(x+t) φ(y+t)                       (discrete SL12a)
           =  Σ_{t,s≥0} φ(x+t) φ(y+s) T_μ(|t-s|),                   T_μ(m) := Σ_{l=1}^{2g} e^{i m θ_l}   (moments of the zero measure of Xi)
    and     T_μ(|i-j|) = q^{-(i+j)/2} · C_{ij},   C_{ij} := 2·sym(Γ_{F^i}·H1)(Γ_{F^j}·H2) − Γ_{F^i}·Γ_{F^j}
                                                  = q^i + q^j − q^{min(i,j)} N_{|i-j|},  N_0 := 2−2g   (Castelnuovo–Severi form on span{Γ_{F^k}} ⊂ NS(X×X))
So V = Aᵀ T_μ A with A_{t,x} = φ(x+t) (half-line Toeplitz of φ = multiplication by Xi followed by P_+), i.e.
    V(x,y) = C̃(D_x, D_y),   D_x := Σ_{t≥0} q^{-t/2} φ(x+t) Γ_{F^t}.
Hodge index (Cor. 1, MIT 18.727 lect. 9) ⇒ C̃ ⪰ 0 ⇒ V ⪰ 0.  Direction: geometry ⇒ positivity ⇒ zeros on the circle.
"""
import numpy as np

def setup(q, th):
    sq = np.sqrt(q); alpha = [sq*np.exp(1j*t) for t in th] + [sq*np.exp(-1j*t) for t in th]; g = len(th)
    P = np.poly1d([1.0])
    for r in alpha: P = P*np.poly1d([-r, 1.0])
    c = P.coeffs[::-1]; ph = {k-g: (c[k]*q**(-k/2)).real for k in range(len(c))}
    return alpha, g, ph

def V_of(ph, g, N=8):
    xs = list(range(-N, g+1))
    V = np.array([[sum((x+y+2*t)*ph.get(x+t, 0)*ph.get(y+t, 0) for t in range(0, N+2*g+2)) for y in xs] for x in xs])
    nz = [i for i in range(len(xs)) if np.abs(V[i]).max() > 1e-12]
    return [xs[i] for i in nz], V[np.ix_(nz, nz)]

if __name__ == "__main__":
    for q, th in [(5.0, [0.7]), (7.0, [0.9, 2.3]), (11.0, [0.4, 1.5, 2.8])]:
        alpha, g, ph = setup(q, th); xs, V = V_of(ph, g); K = 12
        Tmu = lambda m: 2*sum(np.cos(m*t) for t in th)
        W = np.array([[sum(ph.get(x+t, 0)*ph.get(y+s, 0)*Tmu(abs(t-s)) for t in range(K) for s in range(K)) for y in xs] for x in xs])
        Nm = lambda m: 2-2*g if m == 0 else q**m+1-sum(r**m for r in alpha).real
        C = np.array([[q**i+q**j-q**min(i, j)*Nm(abs(i-j)) for j in range(K)] for i in range(K)])
        Ct = np.array([[q**(-(i+j)/2)*C[i, j] for j in range(K)] for i in range(K)])
        T = np.array([[Tmu(abs(i-j)) for j in range(K)] for i in range(K)])
        print(f"genus {g}: |V - AᵀT_μA| = {np.abs(V-W).max():.1e}   |q^-(i+j)/2 C - T_μ| = {np.abs(Ct-T).max():.1e}   min eig V = {np.linalg.eigvalsh(V)[0]:.3e}")
