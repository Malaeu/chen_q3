"""Function-field sibling of SL12a/SL14 (observer, 2026-09-11).

Curve X/F_q of genus g, Z(T)=P(T)/((1-T)(1-qT)).  On the critical circle T=q^{-1/2}e^{iθ}:
    Xi(θ) := P(q^{-1/2}e^{iθ}) e^{-igθ} = Σ_{j=-g}^{g} φ_j e^{ijθ},   φ real, even (functional equation).
Weil RH  ⟺  all zeros θ real.  Discrete kernel (SL12a with x,y,t ∈ Z):
    V(x,y) = Σ_{t≥0} (x+y+2t) φ(x+t) φ(y+t),      H_h(x,y) = q^{h(x+y)} V(x,y).
Observed: min eig H_2 = 0 exactly when all zeros lie on the circle, < 0 otherwise
(genus 1: V collapses to [[2,-a/√q],[-a/√q,2]], det = 4 - a²/q = Hasse bound;
 genus 2: 200/200 random samples agree). DIAGNOSTIC_NEVER_A_PROOF.
"""
import numpy as np

def phi_from_roots(roots, q):
    P = np.poly1d([1.0])
    for r in roots:
        P = P * np.poly1d([-r, 1.0])
    c = P.coeffs[::-1]
    g = len(roots) // 2
    return {k - g: (c[k] * q ** (-k / 2)).real for k in range(len(c))}

def H(ph, q, h=2, N=12):
    g = max(ph); xs = list(range(-N, g + 1)); M = np.zeros((len(xs),) * 2)
    for i, x in enumerate(xs):
        for j, y in enumerate(xs):
            M[i, j] = q ** (h * (x + y)) * sum((x + y + 2 * t) * ph.get(x + t, 0) * ph.get(y + t, 0)
                                               for t in range(0, N + 2 * g + 2))
    return xs, M

if __name__ == "__main__":
    q = 5.0
    for a in [0, 3, 4.47, 4.5, 6]:
        _, M = H({-1: 1.0, 0: -a / np.sqrt(q), 1: 1.0}, q)
        print(f"genus 1, a={a}: min eig H_2 = {np.linalg.eigvalsh(M)[0]: .3e}  (Hasse: {abs(a) <= 2*np.sqrt(q)})")
