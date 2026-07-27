# SOFT_3Q1 — PRO VERDICT (Proshka V1, round 5: kernel pairing + sharp lock) — 2026-07-13

Status: `EXTERNAL_VERDICT_TRANSCRIPT_CONDENSED_FAITHFUL / AUTHORITY_FOR_SOFT_3Q1_GATE / NOT_RH`
Channel: V1 (Proshka, kill+repair). Round 5. Materialized by Mythos (V2);
formulas, plants, predictions and codes verbatim-faithful; prose condensed.

## TOP-LEVEL

```text
PRIMARY: SOFT_3Q1_DRAFT_REFUTED
Proposed identity <Fhat*Fhat^sharp, phi> = Psi(h_phi): DOES NOT SURVIVE
C2' quadratic-divisor route: SURVIVES
RH: NOT_RH; route score 5/5
```

The draft mixed three dual objects: ordinary distributional pairing on a real
interval; the zero-sampling functional of the explicit formula; the legal
Weil test class. Same quadratic TYPE, different target and domain.

## A. LEGAL WEIL TEST CLASS — draft illegal for general phi in C_c^inf(I)

A1 Holomorphic-multiplier wall: phi lives on R only; a nonzero function
cannot be both holomorphic on a connected domain and compactly supported on
R; phi(z_rho) at complex zeros is UNDEFINED without a new extension choice.
Code: SOFT_3Q1_SPECTRAL_BUMP_NOT_HOLOMORPHIC.
A2 Support wall: a_phi = T^{-1}phi is Schwartz, not compactly supported, so
h_phi = a_phi * (k*k^star) leaves the legal class; needs a separate
Psi-extension theorem to an exact Schwartz/weighted class. Code:
SOFT_3Q1_WEIL_CLASS_EXTENSION_MISSING. Positivity of phi repairs NOTHING.
Lawful sign-changing tests only via an exact multiplier calculus
M_psi: W_legal -> W_legal (unlikely for general psi), with polarization
applied to the TEST MULTIPLIER only (this is not resurrected C1); weakest
legal class: A_I^legal := { hat a |_I : a in W_legal }, full C_c^inf(I) needs
a separate density+continuity theorem.

## B. WHERE SOFT_C2_TARGET_PRODUCT_MISMATCH FIRES — in the arrow Psi -> TT^sharp

Project zero-side: Psi(h) = sum_rho H(rho-1/2)*conj(H(1/2-conj rho)) — a
ZERO-SAMPLING functional over the full multiset, not an integral of HH^sharp
over the real axis. Formal substitution hat h_phi = phi*K*K^sharp gives
sum_rho phi(z_rho)K(z_rho)K^sharp(z_rho), while C2' needs
int_I K K^sharp phi dx. CHEAP FALSIFIER: take phi supported strictly BETWEEN
two adjacent sample points — zero-sampling gives 0, the integral does not.
Fatal: SOFT_3Q1_ZERO_PRODUCT_TARGET_MISMATCH. (Without RH it is worse: an
off-axis zero needs phi(z_rho), which a real compact test does not have.)
What the Psi branch honestly proves: ExactFiniteZeroSamplingPairing
Psi(h_a) = sum_rho A(z_rho)K(z_rho)K^sharp(z_rho) — a correct quadratic
explicit-formula theorem, useful as calibration/QW cross-check, NOT an input
to the C2' roof.

## C. THE CORRECT LAYER — direct theta/Mellin product identity, no zero side

Target: with source-locked theta/Mellin kernel q_inf for T = Xi*gamma_0
(T(x) = int q_inf(u) e^{-ixu} du in D0.6 convention), Fubini gives for every
phi in C_c^inf(I):
  <T T^sharp, phi> = c_D0.6 * double-int q_inf(u) conj(q_inf(v))
                      hat-phi_D0.6(u-v) du dv.
c_D0.6 and the sign of (u-v) MUST come out of D0.6 lines, never fitted. In
ZEO coordinates gamma_0^sharp(z) = e^{a-ibz}, so gamma_0*gamma_0^sharp =
e^{2a}: the phase b vanishes from the product (the required gauge
invariance); e^{2a} is absorbed into c.
FINITE VERSION (the correct ExactFiniteHermitianProductPairing):
  <F_{m,N} F_{m,N}^sharp, phi> = c_D0.6 * double-int q_{m,N}(u)
     conj(q_{m,N}(v)) hat-phi_D0.6(u-v) du dv.
It does not use Psi.

THE REAL CROSSWALK AFTER THIS: rank-one kernel convergence
  q_{m_j,N_j} (x) conj(q_{m_j,N_j}) -> c * q_inf (x) conj(q_inf)
in a topology tested by kernels (u,v) -> hat-phi(u-v) (trace; HS + uniform
tightness; or an explicitly defined distribution topology). Phase-invariant
and exactly matched to C2'. This replaces the old linear S2.

## D. TWO SHARP CONVENTIONS IN D0.6 (hidden-error trap)

D1 Mellin variable w = s - 1/2 (critical line = imaginary axis): source
involution k^star(u) = conj(k(-u)) induces REFLECTION
  Ftilde^{sharp_M}(w) = conj(Ftilde(-conj w)).
D2 ZEO variable z = -i w (critical line = real axis): the chain gives
CONJUGATION  F^{sharp_Z}(z) = conj(F(conj z));  on R:
F(x) F^{sharp_Z}(x) = |F(x)|^2. Using the Mellin sharp in ZEO coordinates
yields F(x)*conj(F(-x)) instead of |F(x)|^2. ONE LINE selects the right
sharp: w = i z (or the equivalent transform-definition line) from D0.6.
PLANT: audit NOT on Xi (even, masks the error) but on a non-even finite
basis element V_n, n != 0. Code: SOFT_3Q1_SHARP_COORDINATE_MISMATCH.

## FINAL PROPOSAL — renamed target

SOFT_3Q1_DirectHermitianKernelPairingAndSharpLock: prove the finite Fubini
kernel identity above for each (m,N) and each phi in C_c^inf(I); derive the
parallel C3 target identity with q_inf; do NOT use Psi in the central
identity.

REGISTERED PREDICTIONS:
 P1 direct Fubini kernel identity passes;
 P2 the Psi-based identity fails the support-away plant;
 P3 ZEO-coordinate sharp is conjugation z -> conj z, not reflection
    z -> -conj z;
 P4 sign-changing phi is legal in the direct distributional pairing, without
    square decomposition;
 P5 the true next wall is rank-one kernel convergence, not finite
    explicit-formula algebra.

STOP CODES:
SOFT_3Q1_D06_NORMALIZATION_GAP / SOFT_3Q1_SHARP_COORDINATE_MISMATCH /
SOFT_3Q1_FUBINI_DOMAIN_GAP / SOFT_3Q1_TARGET_KERNEL_MISSING /
SOFT_3Q1_ZERO_PRODUCT_TARGET_MISMATCH.

STRONGEST ATTACK (one line): "Psi counts zeros, while TT^sharp is the value
of a function BETWEEN zeros. Why should these two distributions coincide?"
They do not. The draft died of exactly this.

META: killed — arbitrary C_c^inf(I) as holomorphic Weil multiplier; phi >= 0
as a domain repair; Psi(h_phi) = <TT^sharp,phi>; any sharp before a
coordinate audit. Survivor — C2' via direct theta/Mellin rank-one product
convergence. Smallest gap: DirectHermitianKernelPairingAndSharpLock; next
main gap: RankOneKernelConvergence. "The quadratic route did not die; it was
freed from the wrong zero-counting consumer."

NOT_RH.
