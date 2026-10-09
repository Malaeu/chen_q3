# Q9 own attempt — integrated infinite sieve return

2026-10-09. Independent read-only q05_moment_audit: conditional PASS. Same physical Q8(32)
consumer; Q9 original and source pins are in SOURCE_Q09_CONCLUSION.md.
No full inverse gain, new zero-free region or RH claim.

## Obstruction and exact test

Q9.33 has a finite sixth-power sieve T_R(s) depending on the pair conductor.
A termwise estimate of its infinite extension loses an unaffordable tail
(Q9.35). The weaker actual integral Q9.34 may retain exact cancellation
that its absolute-value sufficient condition Q9.37 discards.

Keep every index and coefficient of Q9.33. Write R=g*b*c, zeta_F^(R)(w)
for zeta_F(w) with Euler factors at primes dividing R removed. There is
NO additional removal of the original fixed set S. Define B_G^infinity(s)
by replacing only

    T_R(s)=sum_(qt<=T_U,(t,R)=1) mu(t) qt^(6s-6)

with

    T_R^infinity(s)=1/zeta_F^(R)(6-6s).                    I1

The latter series is absolutely convergent for Re(s)<5/6. The proposed
identity is on 0<sigma<5/6:

    C_G = 6/(2 pi i L) integral_(sigma)
          U^(1-s) Mellin(tilde rho)(s) B_G^infinity(s) ds. I2

This is an identity of the full integral, not B_G^infinity=B_G pointwise,
and not equality of their absolute integrals in Q9.37.

## I3. Exact vanishing of every added tail term

Fix supported g,b,c,f, with (b,c)=(bc,g)=1, bc!=1, f|g.
Let psi=psi_(b,c), Q=qb*qc and V=U/(qt^6*qf). The primitive full
Poisson identity (Q9.11 at d=e=1), including all element rows, gives

    sum_k bar(psi(k)) tilde rho(V qk/Q)
      = sqrt(Q)/V * Gamma_barpsi * sum_z psi(z) rho(qz/V).

Multiplication by Gamma_psi*psi(f), and Gamma_psi*Gamma_barpsi=psi(-1),
retains the exact phase psi(-fz). For qt>T_U=(b_rho U)^(1/6), every
nonzero z has qz>=1 and

    qz/V = qt^6*qf*qz/U > b_rho.

The z=0 term is zero because rho(0)=0. Thus each ADDED t term has zero
full k sum. No truncation of k, choice of a unit, positivity, or deletion
of a pair is used. Primes from S remain permitted in t and z. The original
coprimality (t,gbc)=1 remains. The weight w_P and f-mask are unchanged.
This argument holds also when the unit projector is zero; those full
radial element sums vanish by their unit orbit.

## I4. Justification at the integral level

For each fixed t, Mellin inversion starts on Re(s)>1. The nonprincipal
primitive L-function is entire; its source polynomial strip growth and
rapid decay of Mellin(tilde rho) permit the shift to any fixed
0<sigma<5/6. The shift is the SAME conditional ordinary Hecke input as
Q9.34, not a zero-free theorem or reciprocal-L bound. There is no pole of
the Mellin transform in this open half-plane. For fixed U,L there are
only finitely many supported g,b,c,f pairs.

On that line, sum_t qt^(6sigma-6) converges. The t-dependent factor has
modulus qt^(6sigma-6), and the other factors have an integrable vertical
majorant for each finite pair. Fubini therefore permits summing the
shifted integrals over t, including the infinite tail. Every tail
integral is exactly zero by I3. This proves I2 conditionally on the
already named analytic input. It does NOT justify absolute rearrangement
of the original double t,k series, which need not be absolutely summable.
Uniformity in the column conductor is unnecessary for this finite-pair
identity; it remains essential for any future quantitative bound.

All common profile derivatives used by Q8 retain the same compact rho
support (or a fixed larger b_rho selected first). I3 remains zero for
t>T_U with that support endpoint. Derivatives of the infinite series
introduce fixed powers of log qt, still summable on a fixed line below
5/6. No rowwise profile supremum is moved inside a signed sum.

## I5. Literal Euler factors and the new target

Let x_p=qp^(s-1), w=6-6s, and write the other pair weights exactly as
Q9.33. On the stated strip,

    T_R^infinity(s)=zeta_F(w)^(-1)
                    product_(p|gbc) (1-x_p^6)^(-1).

Since (g,bc)=1, psi(p)^6=1 for p|g. Combining with the ORIGINAL f-sum,

    sum_(f|g) mu(f) qf^(s-1) psi(f) = product_(p|g)(1-psi(p)x_p),

gives the exact local factor

    product_(p|g) [sum_(j=0)^5 psi(p)^j x_p^j]^(-1)
    * product_(p|bc) (1-x_p^6)^(-1) / zeta_F(w).           I5

These denominators do not vanish when Re(s)<5/6: |x_p|<1 and
|x_p^6|<1, and the zeta reciprocal is in its absolutely convergent
Euler-product half-plane. This is not division across a hypothetical
Siegel zero. At sigma=2/3 the bc product is bounded by zeta_F(2),
uniformly; the g product is at most O_epsilon(qg^epsilon) by the usual
finite-prime/product estimate. Neither estimate supplies cancellation
between different b,c pairs.

A sufficient weaker-than-Q9.37 target is a ONE-SIDED upper bound for the real
WHOLE integral I2, at most H U^(-1/200)(UPD)^epsilon(1+T1)^A.
The full integral is real by the original identity. An absolute integral
bound for B_G^infinity is also sufficient, but not claimed equivalent to
Q9.37. The local simplification opens a candidate Euler-product/multiple
Dirichlet-series approach; no analytic continuation or residue estimate
for such a multiple series has been established here.

## Negative control and limits

If one keeps only a finite k-band, I3 becomes a tail identity rather than
exact zero. If the profile has noncompact support, the elementary support
argument fails and a new tail estimate is required. Replacing the full
integral by integral of absolute values loses I3's cancellation. These
are specific failures of the proposed mechanism, not counterexamples to
RH or to the actual full-profile identity.

The root-number functional equation or a second Poisson transform alone
still returns the same correlation. I2 simplifies an auxiliary finite
factor without shrinking the actual arithmetic sum. Do not count an
identity as a moment gain.

## Separate-contour diagnostic (independently checked)

For 0<sigma<1, separate convexity and positive summation yield only

    |C_G| << P U^(1-sigma) L^(1+sigma)
             max(1,U^(sigma-5/6)) (UPL)^epsilon,

with a logarithm absorbed at sigma=5/6. For L=U^ell, ell>1, the exponent
increases with sigma on either side of5/6. Its infimum at sigma->0+
is p+1+ell, still far above r(1+c)-1/200 on the required interval.
The endpoint sigma=0 is NOT an admitted contour shift: the Fourier
Mellin transform may have a pole there. This diagnostic excludes only
optimization of separate convexity estimates, not joint arithmetic
cancellation. No exterior contour claim is needed.

Review: q05_moment_audit independently checked I1–I5, all original masks,
unit projector, bc!=1 support, fixed-t-first contour shift and Fubini,
common profiles, Euler factors and contour budget. Conditional on the
same ordinary primitive-Hecke analytic source input as Q9.34; no source
certification. The one-sided real-integral target is intentional; a
magnitude bound is sufficient but stronger. Root checked the affine budget
at endpoints/witness with exact rational arithmetic. RH/SP and Q8(32) OPEN.
## Bounded alias return and phase removal

Three shelf dictionaries: Weyl-group multiple Dirichlet series and pair
conductors; metaplectic spectral reciprocity and moving Gauss weights;
bilinear first moments with Mobius/coprimality masks. All three ask.sh
queries returned INCOMPLETE due semantic-index freshness, not absence.

long_positive_alias fetched Gao–Zhao, First moment of central values of
Hecke L-functions with Fixed Order Characters, arXiv:2306.10726v3
(2025-12-01), https://arxiv.org/abs/2306.10726v3 . Root reread the literal
source. Saved Q09_GAO_ZHAO_V3.tex SHA256
bb53701c92069d4b9cd98941b8c4a5494cdee673cbd22f0e5c159a9d95e56140;
downloaded source archive SHA256
14f88ddb526b86d5f76ce5a430681d2f4f33ed2b02a03df583b8604f20a89691.
Theorem1.3 / Eq1.5, TeX236–248, literal condition:
“for $1/2>\Re(\alpha)>0$, all large $X$ and any $\varepsilon>0$”.

PARTIAL ANALOGUE: K=Q(sqrt(-3)), j=6, alpha=1/6+i*tau matches the
L-line2/3+i*tau. The theorem averages a finite ray-character group and
one radial n-window, with a main term involving L(6s,chi^6)/L(1+6s,chi^6).
Our separate b,c windows, mu(b)mu(c), fixed nu pair, w_P, local g factor
and conductor-dependent inverse zeta are not its hypotheses. Arbitrary
coefficient insertion would invalidate its stated average. No mapped
estimate is claimed. Reflected line1/3 is outside its stated alpha range.

Its §2.8, TeX633–655, supplies a precise primitive functional equation.
The additive convention at TeX504–505 is the source's e(z) at S610,
with delta_K=lambda=sqrt(-3). On Pi(b,c)=1, psi is unit-trivial and
Gamma_psi*Gamma_barpsi=psi(-1)=1. Thus exactly

    Gamma_psi Q^(s-1/2) L_F(s,barpsi)
      = 3^(1/2-s)(2pi)^(2s-1) Gamma(1-s)/Gamma(s)
          * L_F(1-s,psi).                               I6

Both orientations are retained, and pairs with Pi=0 remain zero. This
removes the individual Gauss phase and conductor power, at the price of
the reflected line1/3 when s is on2/3. It is an exact source-verified
rewrite, not a smallness bound. Re-expanding and reversing Poisson merely
recovers Q9's identity branch; a new joint arithmetic estimate is needed.

Next bounded test: apply a two-column Dirichlet-series or reciprocity
argument to I2/I5 (optionally I6), retaining every Euler correction and
common profile, and prove an actual one-sided integral gain. First test
its coefficient system against the proposed functional equations; a
single-index first-moment theorem cannot be imported by name.

AUTOPSY: dropped=THEOREM_SHAPE; note=separate convexity and contour optimization fail the target, while the integrated sieve tail cancels exactly; the full coefficient-sensitive pair estimate remains open.
