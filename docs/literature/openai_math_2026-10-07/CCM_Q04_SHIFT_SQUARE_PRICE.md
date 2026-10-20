# Q04 own attempt 1: positive shift squares have an unaffordable explicit return

2026-10-20. Independent bounded PAPER review ccm_q01_return_review: PASS (normalization, full return, PNT price, nonzero original space, scope). Original CCM;
no new full exponent. Geometry reply suggests J*J-E with a paid E. Here is
one literal arithmetic construction and its price, not a claim against all J.

Let H=L2([0,L]), Ic=sum c_j exp(i omega_j t)/sqrt(L), restricted to the
original ran(P). I is isometric there. Define the causal contraction
(V_s f)(t)=1_[s,L](t) f(t-s). Then
c*Q_M(s)c=2 Re <Ic,V_s Ic>. No cyclic replacement is used.
Let a_n=Lambda(n)/sqrt(n)>=0 and s_n=log n, 2<=n<=m.
Define a map into the finite Hilbert direct sum by

    (Jc)_n = sqrt(a_n) (I_H-V_s_n) Ic.

This retains every prime power and every Fourier mixed term. Put

    G = sum_n a_n I*(I_H+V_s_n* V_s_n)I,
    D = P(A_arch-c_A I)P.

On ran(P), expansion of the norm gives exactly

    J*J = G - P A_prime P,
    P K_m P = J*J - E,       E=G-D.

Thus positivity really is built in, but its error is large. If
S_m=sum_(2<=n<=m) a_n, contraction implies

    S_m P <= G <= 2 S_m P,
    E >= [S_m-(50L+8)]P.

Original three constraints do not remove this identity contribution.
For all sufficiently large m, unconditional PNT implies
pi(m)-pi(m/2)>=m/(4 log m). Keeping just these primes (all terms positive),
log p>=L/2 and p^(-1/2)>=m^(-1/2), gives

    S_m >= sqrt(m)/8.

Consequently E >= [sqrt(m)/8-50 log m-8]P eventually.
For M>=2, ran(P) is nonzero (dimension at least 2M-2). Therefore this
particular full E cannot satisfy E<=C_epsilon m^eta P for eta<1/2,
even along any unbounded subsequence. Dropping J*J proves only a square-root
floor. This is an error obstruction, NOT a negative lower bound on K_m:
J*J may cancel its large return. Restoring that correlation is the old debt.

PNT is used only in its ordinary asymptotic form, already checked in
CCM_Q03_ACTUAL_PRIME_BLOCK_OBSTRUCTION.md (DLMF27.12.5).
This test is different from the old boundary-column square completion in
PROSHKA_VERDICT_FULL_CCM_RELATIVE_BOUNDARY_Q04.md(18): that completion used
a proven positive full boundary energy and paid a polylogarithmic return.
Here the literal all-prime difference-map completion has a sqrt(m) return.

Decision: do not select independent causal-shift squares as the desired
positive realization. A different construction must cancel the large scalar
mass before discarding a positive part, or prove a joint lower comparison.
No prime-power, boundary, mixed term or source coefficient was deleted.
