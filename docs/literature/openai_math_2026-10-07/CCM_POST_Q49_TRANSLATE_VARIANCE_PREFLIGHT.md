# Post-Q49: whole-line translate variance loses endpoint separation

2026-10-26. Root derivation; independent bounded PAPER review qualified PASS
by post_q49_translate_audit: identity, original-P family, constants48/pi/8,
whole return and certificate-only scope checked without material findings.
Ordinary PNT, elementary mass bounds and upstream consumer remain inherited.
This tests one certificate, not the sign or spectrum of actual CCM.
Keep N=m,L=log m,M=R=floor(m^epsilon),0<epsilon<1/32 and original P.
Source map: CCM_POST_Q28_EULER_POSITIVITY_PREFLIGHT.md, zero-extended
isometric Fourier synthesis f=Fc on [0,L], c=Pc, ||c||=1.

## Exact pair identity before any modulus

Put a_n=Lambda(n)/sqrt(n), B=sum_(2<=n<=m)a_n>0 and
 V=B^(-1)sum a_n U_(log n), with U unitary translations on L2(R).
No P is inserted between translations. The original source pairing is
 A[c]=2B Re<f,Vf>.
Define D_f=(2B²)^(-1)sum_(n,k<=m)a_n a_k
                       ||U_(log n)f-U_(log k)f||².
Expansion gives D_f=1-||Vf||² exactly. All ordered cross products, actual
prime powers, n=m, and both orientations survive. Thus the proposed
Cauchy completion is A[c]<=2B sqrt(1-D_f).
To obtain an all-vector exponent eta<1/2 this completion would need
1-D_f<=C_epsilon m^(2eta-1) uniformly. Positivity D_f>=0 is insufficient.

## Actual original-P low-band family defeats that certificate

For all sufficiently large m, M>=2. In the FIVE-dimensional Fourier span
|j|<=2 impose the three original complex linear contacts and f(0)=0.
Four homogeneous linear equations leave a nonzero vector; normalize it.
Pad by zero into the ORIGINAL band: it lies in ran P, without changing P.
Periodicity gives f(L)=f(0)=0. Its zero extension belongs to H1(R), with
 ||f'||_2<=4pi/L.
This argument does not require the four constraints to be independent.

Use inherited ordinary PNT B(m)~2sqrt(m), hence B(m)>=sqrt(m) eventually,
and the inherited elementary B(x)<=6sqrt(x). These are scalar prime-mass
inputs, not RH or a variance hypothesis. With t_n=L-log n>=0, layer cake
gives, retaining all prime powers,
 sum a_n t_n²/B = integral_0^infinity 2t B(m exp(-t))/B(m)dt <=48.
(B(x)=0 for x<2; endpoint conventions do not affect this integral.)

The Hilbert-space mean minimizes mean squared distance, so
 D_f<=sum a_n ||U_(log n)f-U_L f||²/B
     <=||f'||² sum a_n t_n²/B <=768pi²/L².
Consequently ||Vf||>=sqrt(1-768pi²/L²) for sufficiently large L.
The numerical allowance 2B sqrt(1-D_f) is therefore of half-power size
on this actual admissible family. No lower bound for A[c] follows.

## Why the lost geometry matters

The translates are close to U_L f, whose support is disjoint from f up to
a null endpoint. A large ||Vf|| does not imply a large Re<f,Vf>.
Indeed, for 0<=t<=L, endpoint Sobolev bounds give
 |<f,U_(L-t)f>|<=||f'||² integral_0^t sqrt(x(t-x))dx
                 =(pi/8)||f'||² t².
Hence on the SAME family
 |A[c]|<=12pi B||f'||²<=192pi³ B/L².
This is only a family-specific upper, not the all-P target or a new power.
It demonstrates the loss at Cauchy without substituting arbitrary weights.

## Full return and scope

If a uniform D lower supplier existed, then
 C0[c]<=2B sqrt(1-D_f)+4 and
 T_>R[c]<=2B sqrt(1-D_f)+b_div,
 PK_mP>=-(2B sup_(c=Pc,||c||=1)sqrt(1-D_f)+50L+8)P.
No second continuous/short charge enters this direct K return.
The family above prevents this whole-line norm certificate from supplying
eta->0; it does not prevent the required ONE-SIDED numerical-range bound.
Retain stronger inherited s_keep<=6sqrt(m)+6m^(1/4) and its usual returns.
Rollback before |<f,Vf>|<=||Vf||: retain the actual signed overlap.
No projected norm barrier, source lower bound, RH claim or route death.
No numerical or interval run is used in this argument.

Duplication screen (post_q49_shift_difference_screen): Q28 already contains
the underlying energy, with E_d/B=D_f+||f-Vf||² exactly. The new evidence
here is the original-P low-band witness and the geometric failure of this
specific norm completion, not the variance identity itself. Q39 incidence
variance and Q48 trace variance are different objects and supply no near-one
lower bound for D_f. Count this as ONE certificate preflight, not three.
