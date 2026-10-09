# HV.27: threshold refinement does not supply the missing inverse gain

2026-10-09. Independent read-only q05_moment_audit F1–F4 conditional PASS.
RH/SP/HV.22/HV.27 OPEN.
Exact starting results: Q3 HV.10, HV.15–20 and HV.31, accepted only
conditionally on plain P and prior masked inverse moment M.
This tests continuing the same cutoff/mask mechanism to its endpoint.

## F1. General thresholds without losing repeated mask factors

Fix C=U^c, c>=1/32, with c bounded and C<=D, and any Y>=1.
Let b=a_(<=Y). For each a<=P, add its distinct primes>Y to b one
at a time, retaining full prime-power columns in every HV.15 increment.
Every intermediate mask divides a. There are at most log(P)/log(7)
steps, so squared triangle costs O(log(2U)), not a new power.
The original incidence #{a<=P:p|a}<=CP/qp includes all powers.
Consequently the same conditional argument yields

 E_delta <=log(2U) P[UC/Y+U^(1/6)L^(5/6)Y^(-11/6)]*loss.       F1

This no longer needs P<Y³. The compressed rough multiplicity must now
count ALL good rough ideals s<=P/qb, not just1,p,p²,pq.
For fixed y>0 and Y=U^y, a constant O(p/y) step bound is possible;
for subpower Y the logarithmic bound above suffices. No masks or
cofinal rows removed; all original units and symbol zeros retained.
Short/slab P argument remains E_KC<=PUC*loss, at fixed bounded c.
B,C,Y are fixed while differentiating L, as in Q3.

## F2. Exact budget frontier

Write L=U^ell, r-1/100<=ell<=r. Relative to H the available gains are

 short part:       5p-c,
 rough K return:   5p-c+y,
 rough M return:   5r c0/6+5(r-ell)/6+11y/6.                 F2

Here p=(r(1+c0)-1)/6 and c0=1/10000. For a strict uniform target
eta=1/200, this particular proof budget requires

 c < min_r(5p-eta)=1783/18750,
 y > (6eta-5*r_min*c0)/11=92/34375.                       F3

The first inequality also suffices for the K return when y>=0.
Both are strict to allow actual epsilon and height losses. They are
requirements to close THIS upper-bound argument, not necessary
conditions on true arithmetic energies.

Thus the short divisor cutoff cannot approach the full column length:
c<.095094 while ell>=1.11. Raising C to L through this same estimate
would cost PUL and exceed the consumer budget. Lowering Y through the
same rough-return bound to U^o(1) also loses the required eta=.005.
For Y=U^o(1), at L=D the available M-return saving is
5r c0/6+o(1). Finite sixth-power inversion HV.31 subtracts precisely
5r c0/6 from that saving. Hence this bound supplies no fixed positive
inverse improvement, even if a smaller eta is proposed.
The o(1) may give subpower changes; no negative lower bound is claimed.

## F3. The surviving unmasked object has genuine rough columns

For C>=1 and any ideal n all of whose prime divisors have norm>C,
the only divisor with norm<=C is1. Therefore exactly

 A_C(n)=1,             j_C(n)=mu(n)-1.                    F4

For squarefree rough n this is0 with an even number of prime factors
and-2 with an odd number; for nonsquarefree rough n it is-1.
This includes every rough prime power, not just squares.
The complex factors nu(n)chi_n(u) remain: nonpositive j_C on this
subfamily is NOT a sign for the actual polynomial or a lower bound
for its high values. Different columns and the complementary nonrough
part may cancel. This test merely exposes coefficients that persist
when the cutoff is tuned; they cannot be relabelled Mobius or plain1.

Q3 HV.29 already shows that the compressed b=1 contribution carries
weight at least cP/logP, using only fixed-field prime counting.
No bound on its actual unmasked high-value excess is provided by F1–F4.

## Decision

Threshold-only continuation is STALLED as a complete supplier.
Do not spend another question optimizing c,y or listing new paid tails.
Next decisive attempt must estimate actual joint HV.27/HV.22, and
must survive the b=1 unmasked subtest with coefficient j_C, including
F4 and all remaining columns. No source independence or RH claimed.

## Bounded alias return

Three shelf dictionaries: Buchstab rough multiplicative parity character large
values; coefficient-sensitive Halasz Montgomery selected Gram multiplicative
characters; Mobius mu convolution pretentious large values conductor aspect.
All three ask.sh runs returned INCOMPLETE, not literature absence.
The bounded independent search returned Montgomery, Mean and large values of
Dirichlet polynomials, Invent. Math. 8 (1969),334–345, Theorem2, equation(11);
Russian translation p124 (large-value discussion continues p125).
Source: https://www.mathnet.ru/php/getFT.phtml?jrnid=mat&paperid=563&what=fullt&option_lang=eng
Fetched PDF SHA256 d834c11d5e3105bb0988c6506860c85dd548d29a6b943ede512ed499042902c1.
Root reread the actual theorem and equation(11). Short literal quote from
p123: «произвольные действительные или комплексные коэффициенты».

EXCLUDED LEAD for the consumer: arbitrary coefficients can structurally hold
L^-1/2 j_C(n)nu(n)W(qn/L)1_(n,b)=1, but the theorem concerns primitive
Dirichlet characters on integers, not our zero-extended Hecke ideal family.
A number-field bridge, conductor control and duplicate-character accounting
are absent. Even an optimistic bridge to its (Q²T+N)*coefficient-energy
budget has N~L and energy U^o(1). At r=113/100, the generic L term exceeds
the necessary b=1 per-mask budget H/P*U^-1/200 by exponent10629/400000.
This rejects that direct upper-budget import only, not cancellation in the
actual polynomial or stronger coefficient-sensitive large-value arguments.
No new supplier; original joint HV22/HV27 remains the return point.
