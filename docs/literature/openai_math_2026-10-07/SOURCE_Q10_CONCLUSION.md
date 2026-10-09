# Source Q10 — joint Euler tail and the remaining signed prefix

2026-10-09. Q10/10 terminal response observed around03:50UTC in SAME
Execute Joint Probe Calculation:
https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6ac5dfb3-b068-83ed-810a-dc77fa77ebbd .
Full965-line original downloaded and read. Final attachment, regenerate,
voice and Antwort abgeschlossen established completion despite stale
service-checking text. No resend/Answer now. This chat is exhausted10/10;
no new request or rollover sent. RH goal ACTIVE; RH/SP OPEN.

## Evidence and checks

Request PROSHKA_EULER_MELLIN_Q10.txt:966397bytes,19568LF,final newline,
SHA256e7f1cb5689d701937c4db7e026e8505abc069caa411abc400a4dd6424d58fd18.
Baselineae06b50e72a1b0b0850f55771366004692eb1aad.
Unchanged original PROSHKA_VERDICT_EULER_MELLIN_Q10.md:86244bytes,965LF,
SHA25626663ebf4b32c6e1d31730b0b75fbfd543214ba49bd69b53293603e081a8bf4a.
Pinned source paper SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3.
Extracted Q10_EULER_EXACT_CHECK.py SHA256
42be39504a2aea50181136a187cbaf47235608eba7a08363c7586c1d42a31a4f.
Root ran python3 /tmp/Q10_EULER_EXACT_CHECK.py on these exact bytes:
1370 finite controls PASS (coefficients, Euler laws and rational budgets).
These do not certify analytic source inputs or an infinite-family bound.

Independent read-only q05_moment_audit: scoped conditional PASS for
§§5–7,9,11. It checked all prime-power pairs in8, original masks and
normalization9, all-powers moving-mask expansion10, joint mass/Rankin,
Cauchy and full g,a,u costs, exact minimum551/100000, finite-prime
partition19 and primary diagonal20, common-profile/scale consumer returns.
Analytic premise remains source lem:inverse-amplification (S12362 onward);
Q10.18 is unproved and no full exponent gain is credited.
Independent read-only long_positive_alias: scoped PASS for §§3–4,8,10.
It checked local Euler/FE/Mellin return3–7, unit factors and S conventions,
full UNWEIGHTED logarithmic Plancherel21, uniform log lower envelope22–24,
all output beyond D0 and precise gcd boundary25. The reciprocal-L
residue29 and diagnostic30 are conditional, with no zeros asserted or
outer cancellation ruled out. This does not certify the source theorem
or the full Gao-Zhao proof; its literal family mismatch remains.

## Exact object and conditional partial bound

Q10.8 retains the actual two-column coprimality coefficient:

 e(p^i,p^j)=1 at i=j=0, -1 when i,j>=1, zero otherwise;
 e(d1,d2)=mu(rad d1) 1_(rad d1=rad d2).

Convolution with both independent Mobius sequences restores
mu(n1)mu(n2) times the indicator of gcd(n1,n2)=1, including all repeated primes. Both shift
norms in Q10.9 are L/(qg qdi); normalizing costs1/(qg sqrt(qd1 qd2)).
The exact amplifier sum over a<=P, mask ag, all sixthfree element rows,
original S-prime row valuations, and (u,g)=1 survive. No (u,a)=1 is added.

The joint absolute Euler mass converges when s1,s2>0 and s1+s2>1.
Rankin gives tail exponents5/24 and5/12, with epsilon slack at boundaries.
Conditional on the same source inverse-amplification/moving-mask moment
used in Q8, Cauchy on the actual two polynomials yields, after ALL g,a,u,

 |R_B| << P(UPD)^epsilon(1+T1)^A
   [U+U^(7/12)L^(5/12)B^(-5/24)+U^(1/6)L^(5/6)B^(-5/12)].

For B=U^(1/40), all r in[28/25,113/100] and
D U^(-1/100)<=L<=D, the raw margins below H U^(-1/200) are
1783/18750,30181/600000,551/100000. Common derivative/profile and
scale returns use the same finite-seminorm moment premise, not a new
rowwise choice. The first U term has no B-saving but is already affordable.

C_G=H_B+R_B leaves the signed prefix Q10.16 on qd1*qd2<B OPEN.
Its unit pair d1=d2=1 has coefficient1; it is not a lower bound for the
whole prefix because other pairs retain signs. Q10.18 is the sufficient
one-sided upper bound H_B<=H U^(-1/200+epsilon)(1+T1)^A.
The available upper envelope still misses it by1/200-5rc/6 at L=D.
No new inverse or high moment exponent is obtained.

The finite-prime alternative K=U^(1/80) retains every power at p<=K.
Omitted primes force qd1*qd2>=B, so the same remainder estimate applies.
Its added primary equal-column diagonal is <=PU(UPD)^epsilon and paid;
it is NOT the zero Gauss diagonal of Q9.

## What the scale and continuation tests do establish

For each actual u,R and finite set of good primes, the FULL logarithmic
scale integral is a Mellin multiplier with

 m(tau)=product_p [1-|z_p/(1-z_p)|^2],
 z_p=psi_u(p) qp^(-1/2-i*tau).

Good primes have qp>=7; zero character values give factor1. Every factor
is positive, and m is between a negative power of log(2K) and1 uniformly
in phases/u/R. Thus this operator alone is not a U^(-eta) contraction
of the FULL unweighted logarithmic L2 norm. Truncating the input at D0
creates output for N>D0; it cannot be discarded. This rejects a specific
full-scale norm shortcut, not the pointwise signed Q10.18 or actual RH.
The local gcd-return law m_p+qp^(-1)/|1-z_p|^2=1 preserves its masks and
requires the original g cutoff boundary to be returned.

The true two-column Dirichlet series has local law1-X-Y and factors as
H(z1,z2)/(L(z1)Lvee(z2)), not a pair of direct L-functions. H is nonzero
in Re(z1),Re(z2)>1/2. Potential inverse-L poles therefore are not killed
by this Euler correction. Q10.29 describes a possible simple-zero
residue, with horizontal sides, multiple zeros and subsequent cross
residues still due; it asserts neither existence of off-line zeros nor
a lower bound for the physical sum. A factorwise hypothetical bound would
need aboutsigma<=.543585 at r=1.1234, plus all polar costs. None is supplied.
The Gao-Zhao radial first-moment theorem still has no coefficient map.

## Decision

Accept only the independently checked conditional long-tail reduction
and the precisely scoped obstruction to unweighted full-scale Euler
contraction in the stated scopes. The new sufficient signed-prefix estimate
Q10.18 and joint polar return remain OPEN. Before another Pro request,
perform a bounded own test on the actual prefix and return via alias-hunt;
do not repeat an unchanged functional-equation/Poisson identity or safe
local factor as a putative power saving. Any forced rollover preserves
the six-field phase and original source history. No new chat sent.

Deliver request, unchanged answer and conclusion together, then pause
response-wait heartbeat after confirmed push. No Lean/Mac Comparator,
Hecke zero-free import or source certification. RH/SP remain OPEN.

AUTOPSY: dropped=THEOREM_SHAPE; note=finite Euler correction has only logarithmic full-scale contraction and possible reciprocal-L poles survive; the short signed prefix estimate remains unproved.
