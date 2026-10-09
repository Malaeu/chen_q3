# Sparse sixth-power amplifier: exact mask return

2026-10-09. Own next attempt after source Q7. Independent read-only
`q05_moment_audit` PASS for A1–A4, against pinned source12362–12468:
exact identities and sufficiency only; A4 itself remains OPEN.
Consumer: Q7(44), actual inverse second moment near r=1.1234, with all
source scale/profile returns. This note tests whether averaging a supplies
a new phase before addressing the remaining u,n,n' correlation.
Source: pinned paper lines12362–12468; Q7(46)–(47).

## Exact common-profile energy

Fix D and a permitted common smooth profile W. All ideals below are the
original primary ideals outside S; u is an element row with q_u~U and
valuations at most five, including the original unit orientations.
Write c_n=mu(n)nu(n)W(q_n/D), keeping every zero extension in chi_n(u).
Let A_S(X) be the EXACT count of allowed primary ideals a with q_a<=X,
zero for X<1, and

    C_U(n,n') = sum_u chi_n(u)^eps conjugate(chi_n'(u)^eps),
    w_P(k) = #{a : q_a<=P, (a,k)=1}.

The sixth-power identity gives chi_n(u*a^6)^eps=
chi_n(u)^eps 1_(n,a)=1, even when (u,a)>1. Consequently

    E(U,P,D) := sum_u sum_(q_a<=P) |M_(u*a^6)(D;W)|^2
       = D^-1 sum_(n,n') c_n conjugate(c_n') C_U(n,n') w_P(nn'). (A1)

No new phase depends on a: it only deletes coefficients with (n,a)>1.
For every ideal k outside S the exact finite inclusion-exclusion identity is

    w_P(k) = sum_(d|rad(k), q_d<=P) mu(d) A_S(P/q_d).           (A2)

This uses the bijection a=d*b among ideals divisible by d. No coprimality
between d and b is introduced. Units are not counted as multiple ideals.
The original n and n' need not be coprime; shared factors occur once in rad(k).
Equations A1–A2 retain precisely the off-diagonal in Q7(47), together with
its diagonal. They do not estimate its signed arithmetic correlation.

## What sparse density fails to buy by itself

As a control ONLY, restrict columns to n having no prime ideal factor p
outside S with q_p<=P. Then (n,a)=1 for every allowed a, so exactly

    E_rough(U,P,D) = A_S(P) sum_u |M_u^rough(D;W)|^2.          (A3)

Every amplifier copy is identical on this column subspace. This is not a
lower bound for the full original Mobius polynomial: cross terms with
the removed columns may cancel, and the source consumer does not allow
silently replacing the polynomial by its rough part. It shows precisely
why counting the sparse image or calling a an independent oscillation
cannot prove a saving without information on the actual column correlation.

## Returns required by the real consumer

For each a, the exact source formula has d|rad(a), coefficient
mu(d)psi_u(d)q_d^-1/2 and scale D/q_d. Thus a fixed-scale A1 estimate
does not alone prove Q7(44). One sufficient stronger input is

    sum_u sum_(q_a<=P) sup_(0<D'<=D) |M_(u*a^6)(D';W)|^2
       << H U^-theta (UD)^epsilon,                          (A4)

H=max(2U,D^(1+c)), P=(H/U)^(1/6), with the same bound for the finite
profile derivatives required by rowwise sigma,t Sobolev. Averaging the
literal source identity then gives H/P times U^-theta, up to arbitrarily
small divisor losses. A positive fixed c chosen with
5c*sup(r)/6<theta/2 retains a positive power gain. All these constants
precede the target; the height order follows the fixed profile family.
Alternatively one can pay the actual d-return directly without a supremum.

A1 is an exact useful kernel, but summing a first has provided no gain.
A4 and the potentially weaker direct d-return bound are OPEN. The next
estimate must exploit mu(n)mu(n') against the actual C_U(n,n'), preserving
w_P(nn'); discarding this mask or absolute-valuing the whole correlation
does not supply that estimate. No new moment, strip, SP or RH result.

## Bounded alias return

Read-only `long_positive_alias` queried the shelf under three dictionaries:
"sparse sixth-power amplifier Mobius inverse polynomial moment saving";
"Mobius weighted sextic Hecke second moment sparse image u a^6";
"sixth-power-free row large values Dirichlet polynomial inverse moment profile masks".
All three returned ASK_STATUS: INCOMPLETE due to semantic-index freshness.
This is not literature absence. A subsequent narrow web search returned
the existing n-th-order/quadratic large-sieve literature; no new outside
theorem was admitted from search snippets.

The concrete locally mapped candidate is source `lem:sextic-large-sieve`,
lines4707–4724: "The sequence is fixed independently of the row k"
(the source typesets k in math). Source lines5298–5337 freeze the powerful
part and preserve the actual moving-prime masks without enlarging S.
For a powerful-part stratum V, they give the conditional source bound

    (UD)^epsilon V^(1/2) {U/V + D + (UD/V)^(2/3)}.

Source URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex .
SHA256 `42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`.
Coefficients are D^-1/2 mu(n)nu(n)chi_n(v)^eps W(q_n/D), fixed across
the remaining squarefree row k; profile derivatives keep this property.
This is a correct partial map, but quantitatively insufficient: at V=1
and 1<r<2 it has exponent 2(1+r)/3, exceeding (1+5r)/6 by (3-r)/6.
V is an actual stratum, not a parameter freely optimized for the whole sum.
Even the most optimistic minimum of its exponent over V misses the target.
No claim is made that the upper bound is attained by the Mobius coefficients.

The next question should ask for actual coefficient-sensitive cancellation
in A1 or a direct paid d-return, not another generic-coefficient sieve or
an assumption that sparse density forces small energy. Stop the candidate
test when it either supplies the full A4 interface or exposes its unpaid
coefficient/mask/scale hypothesis. A4 remains OPEN.

## Reverse column identity (own continuation after Q8 dispatch)

Independent read-only q05_moment_audit PASS for A5–A6 and both directions,
including normalization, ramified zeros, ideal units, scale suprema and
fixed profile derivatives. This addition was NOT included in the sent Q8.
For an allowed ideal a, let E(a) contain every ideal e supported on primes
dividing a, with arbitrary nonnegative valuations. With the same psi_u and
zero extensions, finite local convolution gives

    M_(u*a^6)(D';W)
      = sum_(e in E(a)) psi_u(e) q_e^-1/2 M_u(D'/q_e;W).      (A5)

For each D' the sum is effectively finite by the compact annular support.
At p|a, multiplication of (1-psi_u(p)T) by its geometric inverse removes
that Euler factor; at p|u both factors are one. This proves the identity
including ramified zeros. No smooth asymptotic or zero-free estimate is used.

For every fixed epsilon>0,

    sum_(e in E(a)) |psi_u(e)|/sqrt(q_e)
       <= product_(p|a) (1-q_p^-1/2)^-1 <<_epsilon q_a^epsilon. (A6)

For all sufficiently large prime norms each local factor is at most
q_p^epsilon; the finitely many smaller primes contribute a fixed constant
independent of a,u. Each prime occurs only once in this product.

Let B(U,D;W)=sum_u sup_(0<D'<=D)|M_u(D';W)|^2 and let E_sup be the
left side of A4, on exactly the same u and a families. A5–A6 and ideal
counting give E_sup <<_epsilon P^(1+epsilon) B after relabeling losses.
Conversely the source identity(46), valid at every D', gives
B <<_epsilon P^(-1+epsilon) E_sup by averaging over at least c_S P ideals.
The suprema are legitimate in both directions since q_d,q_e>=1 and the
right-hand scales never exceed D. Both statements apply to each required
fixed profile derivative; the same parameter Sobolev return remains needed.

Thus, up to arbitrarily small powers of P, the sparse supremum energy is
P times the original supremum energy. A4 is a genuine reformulation of the
needed Mobius cancellation, not an automatic dilution by the larger row
ball. This does NOT refute A4 or prohibit exploiting its exact kernel A1.
