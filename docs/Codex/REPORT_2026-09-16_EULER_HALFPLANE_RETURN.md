# Source return: what the exact Euler product actually controls

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; UNIFORM_RAW_MELLIN_OUTER_HALFPLANE_ONLY.
Base: c3533960373df6f59b43c6cb93eb99588330d6bd.
Scope: raw Mellin approximants and the complete source. Not a full-V sign
theorem, new RH implication, canonical admission or new Proshka request.

## S0. Return point, source pins and the actual question

MELLINEDGE excluded every cofinal globally zero-free raw finite family on
Re(s)>5/4. We now ask which actual arithmetic property was lost, and where
restoring it already supplies a proved non-cancellation bound. This is an
analytic source-return audit, not a new literature-hunt result.

Pinned reports in docs/Codex:
- REPORT_2026-09-16_MELLIN_EDGE_PREFLIGHT.md, E0-E3,
  SHA256 a7dfba76bd7018100d312f198987a35e4a08ed163d8f5ade43d0f9244b14c1ff.
- REPORT_2026-09-16_MELLINEDGE_INTAKE.md,
  SHA256 c966f1d94717efab0c291b146a39870a7a1852e67d8acf44ccdc3bb6628d3efc.
- REPORT_2026-09-14_EXACT_RECIPROCAL_PAIRING.md, R2-R6,
  SHA256 3eaccc08a8ee5ced8d828340ba866a16f39d33c7e088c9b324b0bb62c4d7357a.
- NOTE_2026-09-16_EULER_LATTICE_AND_PRIME_INVARIANT.md, sections 1-3,
  SHA256 9b3814f24b5e6941c4bb8506c8a0eeb580c9b88012fa6875d7d8d9d3e219cd11.

Keep the exact raw density r_N of sum_(n<=N) Gamma(2,1)/(pi*n^2), and

 M_N(s)=4*pi^(1-s)*Gamma(s)*D_N(s), Re(s)>0,
 D_N(s)=sum_(n<=N) w_Nn*n^(2-2s)*(s-3/2+delta_Nn),
 w_Nn=(N!)^4/[(N-n)!^2*(N+n)!^2],
 delta_Nn=n*(H_(N+n)-H_(N-n)).                         (S1)

The original complete source has M(s)=2*xi(2s-2), so RH corresponds to
the line Re(s)=5/4. A sign claim for the original V is unchanged and open.

## S1. The complete square-rate series recovers the prime product

The complete density is
 r(t)=sum_(n>=1)(4*pi^2*n^4*t-6*pi*n^2)*exp(-pi*n^2*t).
For sigma=Re(s)>3/2, the integrals of the absolute values of the two
separate terms are bounded by constants depending on sigma times
sum n^(2-2sigma)<infinity. Fubini and elementary Gamma integration give

 M(s)=4*pi^(1-s)*Gamma(s)*(s-3/2)*zeta(2s-2).          (S2)

Thus D(s):=M(s)/(4*pi^(1-s)*Gamma(s)) equals
(s-3/2)*zeta(2s-2), initially on Re(s)>3/2.
This reuses the known Mellin/xi identity; it is not a new formula for xi.

The decisive arithmetic input is unique factorization: expansion of
product_p(1-p^(-z))^(-1) counts each positive integer once. Absolute
convergence for Re(z)>1 permits rearrangement. In exactly that domain,

 zeta(z)=product_p(1-p^(-z))^(-1),
 1/zeta(z)=sum_(n>=1) mu(n)*n^(-z),
 |zeta(z)|>=1/zeta(Re(z)).                            (S3)

Here mu(n) is 0 on numbers with a repeated prime factor and (-1)^k on
products of k distinct primes. The reciprocal series converges absolutely,
and |mu(n)|<=1 proves the bound. This supplies non-cancellation uniformly
over every imaginary height. Primary reference: DLMF 25.2.11,
https://dlmf.nist.gov/25.2.E11 (displayed condition Re(z)>1).
The elementary product/reciprocal argument above is included in full scope.

## S2. The finite weights do not retain multiplicativity

Normalize a_Nn=w_Nn/w_N1, so a_N1=1. For N>=6 define
 q_n=w_(N,n+1)/w_Nn=((N-n)/(N+n+1))^2, 1<=n<N.
Then 0<q_n<1 and q_n decreases strictly. In particular

 a_N6/a_N3=q_3*q_4*q_5<q_1=a_N2,
 a_N6<a_N2*a_N3.                                    (S4)

Since 2 and 3 are coprime, these coefficients cannot be the coefficients
of an ordinary Euler product with independent prime-local factors and
constant term 1. This statement concerns the coefficient series
sum a_Nn*n^(-z), not every conceivable factorization of D_N(s).
The additional delta_Nn term in S1 is also retained throughout below.
S4 identifies a lost algebraic property; by itself it does not cause or
prove the finite zeros. Their existence comes from the accepted obstruction.

## S3. A successful uniform half-plane transfer, with its exact boundary

Claim: for every epsilon>0 there exists N_epsilon such that, for every
N>=N_epsilon, M_N(s) has no zeros anywhere on

                     Re(s)>=3/2+epsilon.              (S5)

All imaginary heights are covered simultaneously. No numerical threshold
or assertion for Re(s)>5/4 is made.

Proof. Put b=3/2+epsilon and a=2*b-2>1. Extend w_Nn by zero for n>N.
The accepted factorial bound is 0<w_Nn<=exp(-n^2/N)<=1 for n<=N.
For each fixed n, w_Nn->1 and delta_Nn->0. Hence dominated convergence
with the summable majorant n^(-a) gives

 A_N:=sum_(n>=1)|1-w_Nn|*n^(-a) ->0.                  (S6)

For n<=N/2, the harmonic sum has 2n terms, each at most 2/N, so
 delta_Nn<=4*n^2/N,
 w_Nn*delta_Nn<=4*(n^2/N)*exp(-n^2/N)<=4/e.
For n>N/2,
 delta_Nn<=N*H_(2N)<=N*(1+log(2N)),
 w_Nn*delta_Nn<=N*(1+log(2N))*exp(-N/4).
The last expression is bounded uniformly for integers N>=1. Therefore
w_Nn*delta_Nn is uniformly bounded and tends to zero for every fixed n.
A second dominated-convergence argument gives

 B_N:=sum_(n<=N)w_Nn*delta_Nn*n^(-a) ->0.             (S7)

For every s with Re(s)>=b, |s|>=b and S1 yields the exact comparison

 |D_N(s)/s-(1-3/(2s))*zeta(2s-2)|
     <=(1+3/(2b))*A_N+B_N/b =:eta_N ->0.              (S8)

The bound is uniform on the entire unbounded half-plane, not merely on
fixed compact sets: all phases were bounded only after extracting the
exact full Euler-product term. No harmonic correction has been dropped.
By S3 and |1-3/(2s)|>=1-3/(2b),

 |(1-3/(2s))*zeta(2s-2)|
     >=(1-3/(2b))/zeta(2b-2)=:m_b>0.                 (S9)

Choose N_epsilon so eta_N<m_b/2 for all N>=N_epsilon. Then D_N(s)/s
never vanishes on that half-plane. Neither s nor Gamma(s) nor pi^(1-s)
vanishes there, so S5 follows. This is an analytic proof, not a grid test.

## S4. What this explains and what it cannot pay

The source property has a complete audit trail:
 unique factorization -> reciprocal absolutely convergent prime product
 -> uniform nonzero modulus S9 -> uniform finite-source transfer S5.
The needed smallness is proved by S6-S8, not inserted as a new assumption.

This supplies a genuine all-height stability region for the SAME raw
approximants. It is consistent with their eventual zeros in 11/8<Re(s)<2:
for each fixed epsilon those zeros, for sufficiently large N, must lie
to the left of 3/2+epsilon. No conclusion on a chosen root's limiting
height or its limiting real part is inferred from this alone.

At b=3/2 the majorant n^(-a)=1/n is not summable and the positive uniform
margin m_b disappears. In 5/4<b<3/2 the same argument is unavailable.
This is a diagnosed limit of this proof, not a proof that every possible
extension must fail. The full source's exact reciprocity gives
M(s)=M(5/2-s), reflecting the already controlled right region into the
left region. It does not fill the central strip. The original full-V
sign is therefore no closer to being proved by S5 alone.

Negative controls: the actual finite coefficients fail S4's required
multiplicativity. Conversely, the positive even g0(x)=exp(-x^2)-exp(-2*x^2)/4
has a reciprocal density t^(-5/4)g0(log(t)/2) and a negative four-node V.
Thus reciprocal symmetry alone also cannot replace the missing transfer.
No additive TN-infinity claim for that control is made.

The next mechanism must spend additional full-source information INSIDE
the unpaid strip, or supply the original all-row energy directly. Names
such as Mellin duality, spectral determinant, multiplicative convolution
or a prime-phase torus are search dictionaries, not sign suppliers.
Existing Brownian, reciprocal, Gram, Schur and finite-prefix results remain
in force. Do not redispatch a request merely to continue S8 past its proved
domain or to demand a globally good raw finite subsequence already excluded.

No new external discovery search, paid call, Lean proof or RH claim.
AUTOPSY: dropped=COUPLING; note=The finite square-rate source loses exact multiplicative Dirichlet coefficients. Restoring the full Euler term proves uniform stability only in its summability half-plane, leaving the critical-strip compensation unpaid.

## Independent acceptance

Candidate SHA256: `68d94cba49b7c5cfc49609f92ebc376f7238164dc8c0fbfb93ec6954b0685cf7`.
Reviewer `/root/sibling5_check`; review SHA256: `fc8ba2dfe89682ffab354c086281a18d54ce331afd9ebcc389c6d858c342d2f6`.
Verdict: ACCEPT_UNIFORM_RAW_MELLIN_HALFPLANE_STABILITY_ONLY.
The parent independently checked S1-S9 and the full-height quantifiers.
Only the status and this receipt were added after review.
This is a proved outer-region diagnostic, not a gain in the full-V sign.
