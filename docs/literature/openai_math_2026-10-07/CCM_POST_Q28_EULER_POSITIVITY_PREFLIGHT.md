# Euler-product positivity: exact source map and return price

2026-10-26. Bounded supplier preflight after Q28. Independent residue_density_supplier
PAPER/source crosswalk PASS: domain, finite energy and complete return fees.
Upstream Q10/Q27 kernel and constants remain inherited.
No new exponent. This is not three new failed attempts or a new Q29.

## Original object and source correspondence

Keep N=m,L=log m,M=R=floor(m^epsilon), the original projector P and
zero-extended Fourier synthesis F from Q10. On ran P let f=Fc. Literal
Q_M(s)=F*(T_s+T_-s)F preserves both shifts and all Fourier mixed entries.
The finite centered target is C0=A+H_decay, where

 A=sum_(n<=m) Lambda(n)/sqrt(n) P Q_M(log n)P,
 integral_1^m x^-1/2 P Q_M(log x)P dx=-H_decay,
 0<=H_decay<=4P.

The probability candidate is the Euler-product compound Poisson law:
for sigma>1, log[zeta(sigma+it)/zeta(sigma)] equals
sum_(p,k>=1) p^(-k sigma)/k [exp(-it k log p)-1].
Its Levy atom weights are Lambda(n)/(log n)n^-sigma, not Lambda(n)/sqrt n.
Multiplying by log n (or differentiating in sigma within absolute
convergence) produces the Mangoldt weights. It supplies a positive jump
measure in sigma>1; it supplies no positivity of the CENTERED difference.
Primary locator: Aoyama--Nakamura, RIMS Kokyuroku Bessatsu B34,
"Zeros of zeta functions and zeta distributions on R^d", Proposition1.7.
https://www.kurims.kyoto-u.ac.jp/~kenkyubu/bessatsu/open/B34/pdf/B34_003.pdf
Primary PDF saved as sources/aoyama_nakamura_B34_003.pdf,936624bytes,
SHA256 fe3b8f79b7ee8e6eceeab51a655e6ac3a2db0c3bded5d98dd0f19e6c06fc86da.
Root read printed pp41--42, Definition1.5 through Proposition1.7.
Short quote, p42: "compound Poisson on". The exact displayed atom formula
is reproduced above. Verified partial correspondence, not an exact CCM
supplier. The published scalar probability variable is Fourier-dual to
log n; our operator averages its two shift orientations against full f.

## Exact finite positive-energy calculation

For every s, translation is unitary on the full zero-extended L2 space:

 ||f-T_s f||²=2||c||²-c*P Q_M(s)Pc.

Thus define the full discrete and continuous energies, BOTH nonnegative,

 Ed[f]=sum_(n<=m) Lambda(n)/sqrt n ||f-T_log n f||²,
 Ec[f]=integral_1^m x^-1/2 ||f-T_log x f||² dx.

With Bd=sum_(n<=m)Lambda(n)/sqrt n and Bc=2(sqrt m-1), exactly

 c*C0*c=2(Bd-Bc)||c||²-(Ed[f]-Ec[f]),
 Ec[f]=2Bc||c||²+c*H_decay*c.

Every prime power, cutoff and mixed shift term remains. Even the n=m
atom is retained: Q_M(L)=0 but its TWO energy diagonals remain. Positivity
of Ed and Ec separately does not order their difference. Dropping Ed and
substituting the exact Ec restores only

 C0 <= 2Bd P+H_decay <= (12sqrt m+4)P.

Here the last inequality uses the inherited elementary Chebyshev bound;
it is the old Q11 positive-energy-drop completion, not a new result.
After returning C0 to T_>R, H_decay cancels and the same upper is
T_>R <= (12sqrt m+b_m)P. The full K floor remains
PKP >= -(12sqrt m+50L+8)P. No mixed term is silently dropped as zero.

## Staying in the probability theorem's half-plane

An alternative direct norm transfer from sigma=1+1/L multiplies each
finite coefficient by n^(sigma-1/2)<=e sqrt m. Since ||Q_M(s)||<=2 and
the inherited source bound sum Lambda(n)n^(-1-1/L)<=6L holds, this route
costs at most 12e sqrt m L. Returning from the probability half-plane is
therefore no better than the existing fallback. Positivity after an
infinite analytic continuation to sigma=1/2 is NOT supplied by the theorem.
For finite sums at sigma=1/2 positivity of Ed is immediate, but the exact
centered difference above shows why that fact does not finish the task.

## Scope and decision

The missing comparison is Ed-Ec >= 2(Bd-Bc)||c||² minus a
vanishing-exponent fee, uniformly on original P. This is the original
signed source debt in energy coordinates, not a newly proved supplier.
As a negative control, two nonnegative measures may have either sign in
their difference; positive definiteness is not preserved by subtraction.
This diagnoses the generic inference only, not actual primes or CCM.

Shelf comparison: Q11 already excludes dropping positive energy plus
independently paying the full defect as a sub-half-power certificate.
The September self-decomposable theta-law cards concern a different
probability law and do not supply this centered Mangoldt comparison.
Q20's Selberg/convolution/log-derivative mechanism was also already tested;
do not count re-reading it as another experiment. No new inequality is
obtained here. Keep the exact C0 and seek a source-dependent JOINT comparison
before positive-energy disposal. No new Proshka request has been sent.
