# Q03 waiting result: an actual prime block cannot have a subpower upper bound

2026-10-20. Root derivation; independent bounded PAPER review by
ccm_q01_return_review: PASS (factorization, normalization, PNT transfer, scope).
Pro Q03 is running; this note has NOT been sent as a second prompt.

## Statement with original source preserved

Let L=log m>=2pi, w=2pi/L and M>=2. Use the original three-constraint
projector P on the original modes |j|<=M, with N=m. Put
alpha=exp(-1/2), beta=exp(-1/4), and define the literal uncentered block

    B_m=sum_(alpha*m<n<=beta*m) Lambda(n)/sqrt(n) P Q_M(log n)P.

All prime powers in this interval are included. There is an absolute c>0
such that for every sufficiently large integer m,

    lambda_max(B_m|ran P) >= c sqrt(m)/(log m)^9.              (1)

Consequently this BLOCK does not admit B_m<=K m^eta P eventually, for any
fixed finite K and eta<1/2. In particular it cannot be independently paid
with eta(epsilon)->0 along M=floor(m^epsilon), for small fixed epsilon.
The statement also excludes a cofinal such block bound, since (1) is eventual.

THIS IS NOT A LOWER BOUND FOR THE COMPLETE A_prime, T_gtR OR V.

## Exact admissible vector and uniform log interval

Take the even real Fourier polynomial from CCM_Q03_ENDPOINT_SIGN_TEST.md:

    f(t)=-3/4+(1+4w^2)cos(wt)-(1/4+4w^2)cos(2wt).

Its endpoint value and both exponential moments vanish exactly, so its
coefficient vector belongs to the ORIGINAL ran(P). Let Fc=f/||f||_2.
The exact factorization is

    f(t)=(1-cos wt)[12w^2-(1/2+8w^2)(1-cos wt)].

For |t|<=1/2 and 0<w<=1, elementary cosine bounds give

    w^2 t^2/3 <= 1-cos(wt) <= w^2 t^2/2,
    (1/2+8w^2)(1-cos wt) <=17w^2/16,
    f(t)>=(10/3)w^4 t^2.

The lower cosine bound follows, for example, from
1-cos x>=x^2/2-x^4/24>=x^2/3 for |x|<=1/2.
For h in [1/4,1/2], periodicity and evenness therefore yield

 q_f(L-h)=2 integral_0^h f(t-h)f(t)dt
          >=(200/9)w^8 integral_0^h t^2(h-t)^2dt
          =(20/27)w^8 h^5.

Orthogonality gives

 ||f||_2^2=L[9/16+((1+4w^2)^2+(1/4+4w^2)^2)/2]
           <=(707/32)L <23L.

Thus for the same UNIT vector c at this cell, uniformly in h in [1/4,1/2],

 c*Q_M(L-h)c >= kappa L^(-9),
 kappa=20(2pi)^8/(621*4^5)>0.                              (2)

Unlike the earlier Taylor sign test, (2) has a fixed log-width and explicit
normalization; no unknown L-dependent small neighborhood is used.
All mixed Fourier terms are retained through the exact overlap formula.

## Actual primes, not a synthetic signed source

Every n in (alpha*m,beta*m] has h=log(m/n) in [1/4,1/2), so (2) applies.
All Lambda(n) are nonnegative, and every summand has positive quadratic form
on c. Retaining just primes gives a legitimate lower bound for this block.
Unconditional PNT pi(x)~x/log x implies, for these fixed alpha,beta,

    pi(beta*m)-pi(alpha*m) >= (beta-alpha)m/(2L)

for every sufficiently large m. Each retained prime has log p>=L/2 and
p^(-1/2)>=m^(-1/2). Hence

 c*B_m c >= kappa L^(-9) * (L/2)/sqrt(m)
                     * (beta-alpha)m/(2L)
          =kappa(beta-alpha)sqrt(m)/(4L^9).

Rayleigh's principle proves (1) with c=kappa(beta-alpha)/4.
For eta<1/2, m^(1/2-eta)/L^9 diverges, proving the stated exclusion.
No numerical threshold for eventual PNT is claimed, and no RH-strength
error term is used.

PNT source live-read by root: NIST DLMF 27.12.5,
https://dlmf.nist.gov/27.12#E5 (20 October 2026). Its unconditional
pi(x)-li(x)=O(x exp(-c sqrt(log x))) implies the elementary asymptotic used
above. Independent reviewer checked the transfer; root checked the source.

## What this forces, and what it does not

A proof that separately upper-bounds EVERY raw prime block by subpower
cannot work for this partition. Some genuine signed comparison across blocks,
or centering BEFORE estimating them, is essential for such an approach.
This is stronger than an arbitrary-coefficient counterexample: the block
uses the actual von Mangoldt weights and actual original projected modes.

It does not contradict the target full CCM estimate. On this same vector,
other blocks can be negative; summing them is not a Loewner monotone operation
because Q_M(s) is not positive semidefinite. In fact the existing full-window
continuous identities already show cancellation of large smooth pieces.
Do not infer any lower bound for T_gtR by restricting the global short-divisor
return: that return was paid globally, not blockwise. No term of the production
source has been removed and no new source has replaced it.

No new full exponent, SP/RH result, or forbidden actual-cancellation claim.
Use (1) as a discriminator for the eventual Q03 answer, not a new demand that
it prove a false independent-block lemma. No additional Pro message sent.
