#!/usr/bin/env python3
"""Observer check 2026-09-12 (rule 13): the SIBLING2 Toeplitz form T_mu(i-j) = sum_l e^{i(i-j)theta_l}
equals the normalized ROSATI trace form on Frobenius powers, q^{-(i+j)/2} Tr(pi^i (pi^j)^dagger), dagger = q pi^{-1}.
Consequence: the surface X x X is bookkeeping; the sign lives in (End(J), dagger, Tr) = an algebra with a positive involution.
DIAGNOSTIC_NEVER_A_PROOF (the identity itself is one line: (q/alpha)^j = conj(alpha)^j on |alpha|=sqrt q)."""
import cmath, math, random
random.seed(1); q, g = 7, 3
thetas = [random.uniform(0, math.pi) for _ in range(g)]
alphas = []
for th in thetas:
    a = math.sqrt(q)*cmath.exp(1j*th); alphas += [a, a.conjugate()]
T_mu = lambda k: sum(cmath.exp(1j*k*th)+cmath.exp(-1j*k*th) for th in thetas)
rosati = lambda i, j: sum(a**i*(q/a)**j for a in alphas)
worst = max(abs(rosati(i, j)*q**(-(i+j)/2) - T_mu(i-j)) for i in range(6) for j in range(6))
print(f"genus {g}, q={q}: max|q^-(i+j)/2 Tr(pi^i pi^j^dagger) - T_mu(i-j)|, 0<=i,j<6 = {worst:.2e}")
