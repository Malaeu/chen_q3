# Reciprocity singles out shape two among full integer convolution powers

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; ACCEPT_SCOPED_INTEGER_SHAPE_AND_SCALE_RECIPROCITY_CLASSIFICATION_ONLY.
Base: b6951fed83ac2065e7f36ff53f668ef64d36d6fb.
Isolated research for the original all-finite-complex V objective.

## 1. Bounded question and source mapping

The source's additive total positivity and its reciprocal identity are both
proved, but their joint transfer to full V positivity is open. We test one
explicit family in which the first property survives at every order: change
the number of independent copies of the shape-one source and allow a positive
rescaling. Can this family give another reciprocal source, possibly a control
for the missing joint implication? The stopping condition is an exact
classification within this family, not a classification of every PF source.

Input: HYPERBOLIC_SOURCE_COMPENSATION L1 gives the full source laws
 T_m = sum_(n>=1) Gamma(m,1)/(pi*n^2),    m=1,2,...,
 L_m(s) = [sqrt(pi*s)/sinh(sqrt(pi*s))]^m.
All gamma variables are independent. Let r_m be the density; r_1=h and
r_2=r is our actual source. Since r_m=h convolved with itself m times,
additive TN-infinity is preserved by the already proved convolution theorem.
Positive scaling also preserves all its ordered minors.

The test allows every integer m>=1, every c>0 and every real kappa. Define
 q_(m,c)(t)=c^(-1) r_m(t/c), t>0.
No cutoff, finite truncation of the square-rate product, extra power tilt,
or change of the target V is introduced.

**Claim.** If
 q_(m,c)(1/t)=t^kappa q_(m,c)(t) for every t>0,               (R1)
then m=2, c=1 and kappa=5/2. Conversely these parameters satisfy (R1) by
the actual theta identity. Thus this test family has precisely the original
reciprocal source. A positive scalar normalization would cancel from (R1).

The old negative-V Gaussian control is outside this family: its inverse log
density fails additive TN2. This result constructs no new negative control;
it excludes varying integer shape/scale as a way to obtain one while retaining
reciprocity. It proves no general joint-TN/reciprocity theorem and no V sign.

## 2. Two-term large-t expansion with the complete source retained

Write T_m=G+W, where G has Gamma(shape m, rate pi) and
W=sum_(n>=2) Gamma(m,1)/(pi*n^2). For every eta<3pi,
E exp((pi+eta)W) is finite. The full product telescopes:
 E exp(pi W)=product_(n>=2)(1-1/n^2)^(-m)=2^m.
Under the normalized exponential tilt of W by exp(pi W),
 E_tilt W=(m/pi) sum_(n>=2)1/(n^2-1)=3m/(4pi).

Convolution with the first gamma density gives exactly
 r_m(t)=pi^m exp(-pi*t)/Gamma(m)
          * E[exp(pi W)(t-W)^(m-1) 1_(W<t)].              (R2)
The power is a polynomial since m is an integer. Expand it and extend each
of its finitely many tilted moments from W<t to all W. Exponential moments
at pi+eta bound the omitted parts exponentially, times a fixed polynomial.
Consequently, for each fixed m,
 r_m(t)=A_m t^(m-1) exp(-pi*t)
         * [1 - 3m(m-1)/(4pi*t) + O(t^(-2))],            (R3)
 A_m=(2pi)^m/Gamma(m)>0.
For m=1 the first correction is zero and the remaining relative error is
exponentially small; for m=2 the polynomial has only two terms. Both cases
still satisfy the stated O(t^(-2)) remainder. No uniformity in m is needed.

## 3. Two-term small-t expansion, including its full-series remainder

For real s>0 expand the entire positive geometric factor:
 L_m(s)=2^m pi^(m/2) s^(m/2)
         * sum_(j>=0) binom(m+j-1,j) exp(-a_j sqrt(s)),
 a_j=(m+2j)sqrt(pi).                                    (R4)
Use the elementary inverse-Gaussian Laplace pair
 ell_a(t)=a/(2sqrt(pi)) t^(-3/2) exp(-a^2/(4t)),
 integral_0^infinity exp(-s*t) ell_a(t)dt=exp(-a sqrt(s)).
Repeated differentiation with respect to a gives
 g_m(a,t)=(-partial_a)^m ell_a(t),
 Laplace(g_m(a,.))(s)=s^(m/2)exp(-a sqrt(s)).
Each derivative is a finite polynomial times the displayed Gaussian.
Its first two terms for fixed a>0, t down to zero, are
 g_m(a,t)=a^(m+1)/(2^(m+1)sqrt(pi)) t^(-m-3/2)
          exp(-a^2/(4t))
          * [1-m(m+1)t/a^2+O(t^2)].                     (R5)
For m=1,2 the remaining polynomial terms vanish; the error convention is
still valid. Formula (R5) follows either by induction in m or by taking the
two highest powers of a after the m derivatives of a exp(-a^2/(4t)).

Termwise inversion of (R4) is justified, rather than presumed. Each monomial
in g_m is a constant times
 a^(m+1-2k) t^(-m-3/2+k) exp(-a^2/(4t)),
 0<=k<=floor((m+1)/2).
For fixed s>0 split its exponential into two equal parts. The inequality
 s*t/2+a^2/(8t)>=a sqrt(s)/2
and substitution u=a^2/(8t) show that its absolute Laplace integral is at
most a fixed power of a times exp(-a sqrt(s)/2). This is summable over a_j
even after multiplication by binom(m+j-1,j), which grows polynomially.
Thus the series of g_m has an absolutely convergent weighted L1 integral;
its Laplace transform is (R4). Laplace uniqueness identifies the sum with
r_m. The same Gaussian estimates give locally uniform convergence in t>0.

For 0<t<=1 the j>=1 terms obey a stronger endpoint estimate. Their
exponential gap relative to j=0 is
 (a_j^2-a_0^2)/(4t)=pi*j*(m+j)/t >= pi*(m+1)*j/t.
All their coefficients grow polynomially in j. Hence their sum is bounded
by a constant times
 t^(-m-3/2) exp(-m^2*pi/(4t)) exp(-pi*(m+1)/t).
This controls the complete remaining series, not merely its first mode.

Taking a_0=m sqrt(pi) in (R5) therefore yields
 r_m(t)=C_m t^(-m-3/2) exp(-m^2*pi/(4t))
          * [1-(m+1)t/(m*pi)+O(t^2)],                   (R6)
 C_m=m^(m+1) pi^m/2>0.

## 4. Matching the exact reciprocal law forces the parameters

Scaling (R3) and (R6) gives, as t tends to infinity,
 q_(m,c)(t)=A_m c^(-m) t^(m-1) exp(-pi*t/c)
          * [1-3m(m-1)c/(4pi*t)+O(t^(-2))],             (R7)
 q_(m,c)(1/t)=C_m c^(m+1/2) t^(m+3/2)
          exp(-m^2*pi*c*t/4)
          * [1-(m+1)/(m*pi*c*t)+O(t^(-2))].             (R8)
If (R1) holds identically, comparison first of exponential rates and then
of powers of t gives
 c=2/m,     kappa=5/2.                                  (R9)
The leading positive constants must also agree. Dividing the two expansions
by this common leading factor, comparison of their t^(-1) coefficients is
 - (m+1)/(2pi) = - 3(m-1)/(2pi).
It forces m+1=3(m-1), hence m=2 and c=1. At these parameters A_2=C_2=4pi^2,
so there is no leading-constant mismatch; the exact theta identity supplies
the converse, not merely agreement of asymptotics.

## 5. What this changes and what it does not

Before the test, changing convolution shape while retaining full additive
TN was an untested possible source deformation for the joint implication.
The exact tail comparison now rules out that deformation within all integer
shapes and all positive scales. This includes all even levels of the existing
coupled-field ladder. They are exact auxiliary sources, but they do not each
inherit the original reciprocal symmetry after any positive rescaling.

The proof uses the full square-rate product twice: its tilted remainder
mean 3m/(4pi), and the hyperbolic small-t coefficients. It does not identify
an arithmetic prime contribution or produce a lower bound for full V.
No claim that this is a previously unknown theorem is made.

This closes only the stated source-family test. It does not classify all
TN-infinity reciprocal densities, show their uniqueness in a larger class,
give a new Proshka proof task, or reduce the remaining RH-strength statement.
The exact positive mechanism carrying these source properties to all-finite
V remains absent. No extra ladder levels are to be inferred from this result.

## Independent acceptance

Candidate SHA256: `a64fa0afdea7a7f1ce20c8f2b6284fc76eff32b114ea4618716b0c158df345a1`.
Review SHA256: `5f8b69d32909897ed70678d1127e79bf9e3d37b2d4749209d13d09e21f84f513`.
Reviewer: `/root/sibling5_check`. Verdict: ACCEPT_SCOPED_INTEGER_SHAPE_AND_SCALE_RECIPROCITY_CLASSIFICATION_ONLY.
The parent read the complete review and checked the endpoint estimates,
the full inverse-Laplace series bound and the coefficient comparison. Only
status and this receipt were added after review. No canonical admission,
Lean certification or full-V sign conclusion is asserted.
