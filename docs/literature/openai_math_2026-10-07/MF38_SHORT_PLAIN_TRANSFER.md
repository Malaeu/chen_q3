# MF.38 short plain transfer and the exact long coefficient

2026-10-09. Independent read-only mobius_short_transfer S1–S4 conditional PASS.
RH/SP/MB.34/MF.38 OPEN.
Consumer and definitions: Q2 MF.5–9, MF.34–43; same actual Omega, M,
fixed arithmetic data, common profiles and upper-scale band.
This tests the plain-polynomial transfer before another Pro question.

## S1. Paid short part on the original sparse support

Write M_v=K_B,v+J_B,v using exact MF.7, where K has qa<=B and
J has qa>B, with every mu2=mu*mu coefficient and character zero retained.
Choose B=U^(1/32), independent of L and of the row.
By MF.35, late Omega support contains no principal inducing rows.
Thus the conditional plain input P and MF.8 apply to its short part:

 sum_(v in R0) |K_B,v|^4 <=H B² U^eps(1+T1)^A.

Cauchy with Omega<=C and sum Omega<=C PU gives

 E_K:=sum Omega|K_B|² <=(PU)^(1/2)(HB²)^(1/2)*loss
     =H U^(-5p/2+1/32)*loss
     <=H U^(-5639/300000+eps)(1+T1)^A.             S1

This is conditional on plain P, not the raw R used for Q2's different
large-common-divisor tail. Their equal exponents come from the same
chosen excess1/16; the two tails are not the same mathematical object.
The margin relative eta=1/200 is4139/300000.
Original fixed-S principal rows vanish in Omega, not in raw R4;
no transformed moving-twist rows have been discarded.

## S2. What remains is equivalent at the required energy budget

The triangle inequality in weighted l2 gives exactly

 |sqrt(E_M)-sqrt(E_J)| <=sqrt(E_K).                 S2

Consequently an upper energy bound H U^(-eta+eps)*height for either
M or J implies the same exponent for the other, with S1 paid.
Cross terms are included by the norm inequality, not declared zero.
This is a conditional equivalence at the target budget, not a new gain.

For every V>=0, pointwise for complex M=K+J,

 (|M|²-V)+ <=2|K|²+2(|J|²-V/2)+,
 (|J|²-V)+ <=2|K|²+2(|M|²-V/2)+.                  S3

Proof: |M|²<=2|K|²+2|J|² and (a+b)+<=a+b+ for a>=0;
then interchange M,J using J=M-K. After weighting by original Omega,
a bound for the actual J excess above V0/2 suffices for MF.38.
Conversely MF.38 bounds total E_M after its paid clipped part, hence
bounds E_J and its excess. Constant changes to V0 do not alter that
paid small-value budget. The pointwise inequality alone does not
transfer the identical cutoff; the direct forward contract uses V0/2.
No tail estimate has been established.

## S3. The long coefficient cannot be replaced by Mobius

Expand the ordinary S polynomial before taking a norm. Exactly,

 J_B,v(L)=L^(-1/2) sum_n psi_v(n) W(qn/L) j_B(n),
 j_B(n)=sum_(a|n,qa>B) mu2(a)
       =mu(n)-sum_(a|n,qa<=B)mu2(a).                S4

All ideal divisors, including square factors, occur. For a good prime
qp>B (and B>=1), j_B(p)=-2 and j_B(p²)=-1. The latter follows from
mu2(p)+mu2(p²)=-2+1, or from mu(p²)-mu2(1)=0-1.
For B<qp<=beta L, the prime column therefore remains with its full
original character and doubled coefficient. Whenever p² meets the
annular window, that square column remains nonzero as well.
This is no counterexample to small E_J; signs and phases may cancel.
It does prevent feeding J into the inverse source lemma by silently
calling j_B a squarefree Mobius coefficient or smooth profile.

## S4. Profiles, masks and next decisive action

B depends on U only, so log-L differentiation commutes with the finite
convolution split and sends W to -W/2-yW'. All bounds first hold for
the common derivative family. Then positive energy Sobolev may be used;
no differentiation of the positive-part threshold is needed.
The fixed norm twists, both character orientations, unit labels and
all zero extensions are retained by S4. No new (u,a)=1 restriction.

Decision: plain P pays K, but supplies no estimate for J's actual
weighted high values. The simple short/long transfer is STALLED as a
complete supplier. A next attempt must exploit j_B jointly with the
sparse row family, or directly control MF.38; it cannot count the
change of representation or the paid short part as full progress.

## Bounded alias return

long_positive_alias searched three object dictionaries: restricted weak-type
character transform/large-value Gram; multiplicative sparse-image
anti-concentration; Mobius convolution-tail exceptional-character values.
All three deferred shelf searches returned ASK_STATUS INCOMPLETE due to
q3_docs freshness, not absence. No external source was adopted.

Best partial source: pinned paper.tex S4708–4724, sextic large sieve,
SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex
Quote: "The sequence is fixed independently of the row".
It bounds squarefree rows and squarefree columns by
(KD)^eps[K+D+(KD)^(2/3)] sum|c_n|². Root reread4700–4738.
Our jB is fixed across rows, but not squarefree-supported; ua^6 rows
also are not squarefree. Free restriction of row/support sets does not
extend the theorem to them. Even an optimistic K~H,D~L proxy has
cross exponent2(h+ell)/3 about1.49, above h-eta about1.115.
This is an insufficient upper budget, not a lower bound for actual J.
A synthetic vector aligned with one row may spike despite fixed
coefficients; it is a negative control, not our arithmetic polynomial.
Classification: conditional partial mechanism; no mapped supplier.
Next bounded test: actual masked J weighted excess above V0/2, retaining
jB(p²), all ua masks and common derivatives; no generic sieve import.
