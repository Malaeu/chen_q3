# Q9 cross-product conductor test

2026-10-09. Independent q05_moment_audit PASS with the pair-profile qualification below. RH/SP/MB34 OPEN. No Q10 sent.

The remaining target CF20 couples different products k and their orientations. Before invoking another joint dispersion estimate, compute its actual local conductor and retain every zero. The accepted Q9 CF11 primitive squarefree character bound is the supplier used here, not a new unverified moment theorem.

## C1. Exact conductor and complementary mask

Let i=(n,m), j=(n',m'), with each pair individually coprime, squarefree and good. Set k=nm,k'=n'm',Q=q_k,Q'=q_k', and beta_i=chi_n conjugate(chi_m). Define ideal products

    a=gcd(n,n') gcd(m,m'),
    b=gcd(n,m') gcd(m,n').

Then a,b are coprime squarefree ideals. Same-orientation shared primes contribute exponent0 to beta_i conjugate(beta_j), opposite-orientation shared primes exponent±2, and primes in only one product exponent±1. Consequently

    beta_i(v) conjugate(beta_j(v)) = 1_((v,a)=1) xi_ij(v),
    r = lcm(k,k')/a,      q_r=QQ'/(q_a² q_b).

Here xi_ij is the primitive character modulo r with those nonzero exponents, extended by zero on nonunits. The complementary a-mask MUST remain even though its local exponent cancels. Identical pairs are exactly r=1; their principal masked diagonal is treated directly, not with the nonprincipal Poisson estimate.

For nonidentical pairs Q9 CF11 gives, for a fixed smooth radial Schwartz profile,

    |sum_(v sf elements) Phi(q_v/J) beta_i(v) conjugate(beta_j(v))|
      <= C_(Phi,eps) (QQ')^eps min(J, sqrt(J) q_r^(1/4)).

All units and S-primes of the row remain. Neither character inversion at zero nor reciprocal-L bounds are used.

## C2. Quantitative discrimination on a genuine scale diagnostic

At g=d=e=t=1, use column dyads q_n,q_m,q_n',q_m'~X=L and natural frequency length J~X²/U. Both original windows are retained in the coefficients; this is a diagnostic entrance, not an independently required signed subtarget. The second branch divided by the natural row scale J is, up to fixed constants and declared small losses,

    U^(1/2)/(q_a² q_b)^(1/4).

Thus a fixed power saving from THIS envelope requires q_a² q_b to exceed U² by a power margin. There is no literal sharp constant-one threshold implicit in the asymptotic notation.

- Disjoint products: a=b=1. The second branch exceeds J, so this estimate supplies only the trivial J branch. This says nothing about the true correlation's size or sign.
- Swapped orientations: n'=m,m'=n, so a=1,b=k,r=k. The relative second branch is sqrt(U/X), recovering the fixed-product cubic situation from Q9.
- Identical orientations: r=1, principal masked diagonal, excluded from the nonprincipal estimate. It is not the original n=m diagonal of the original energy.

Improving within-product cubic entries alone does not automatically estimate the generic between-product entries. No count or mass of the shared-prime sectors is asserted, and no source lower bound or impossibility theorem follows.

## C3. Real profiles and cutoffs

The actual cross-Gram pair weight is Phi(q_v/J_i) conjugate(Phi(q_v/J_j)), where J_i=Q/(Y q_t²) and J_j=Q'/(Y q_t²), not a universally fixed single Phi. On matched product dyads, normalizing to one reference J puts both scale ratios in a fixed compact range; the product profiles have uniformly bounded finite seminorms and the same estimate applies. Different external labels/scales require their own dyadic decomposition and costs.

The original hard frequency cap is not differentiated or silently discarded. Q9 paid its extension for the original linear sum, not automatically for a new squared cross-family. A use of this smooth cross-Gram in CF20 requires an explicit pair-level cutoff return or a carefully justified use of the already-extended linear expression. No full signed aggregate is bounded here.

## Scope and next question

Root derived the local exponent table; q05_moment_audit independently verified the conductor, mask, primitive/nonprincipal distinction, swapped and disjoint controls, threshold, and pair-profile caveat. Source: Q9 CF10–14, original SHA2560a4b1bdb68b95368bd0f2ad79c98f974fab62d976bad2d03b122418cb4723258. Its uniform primitive character proof uses the pinned Eisenstein source, not a certified Hecke moment.

A stronger short-sum bound is a candidate only after its modulus, lattice, shape, squarefree sieve and all outer costs match. An optimistic number-field volume threshold J>q_r^(1/4) is not itself a theorem and cannot be substituted for a rational box-side threshold. The full signed k/orientation problem remains open.

## Primary-source candidate: excluded direct quadratic-form import

Heath-Brown, arXiv:1411.4816v1, Theorem3, https://arxiv.org/html/1411.4816v1 . Downloaded HTML532053bytes, SHA256e59382198173186c06d64a76a7adf09c1955ae66a3dd2297c244c89bfd9a1d09. Exact hypothesis excerpt: “a binary quadratic form with” followed by the determinant-coprimality condition. For primitive rational character modulo odd squarefree q and convex region in a disc of radius B, the bound is B^(2-1/h)q^((h+2)/(4h²)+eps), for integer h>=3 and q^(1/4+1/(2h))<=B<=q^(5/12+1/(2h)). Here h is the Burgess parameter, not our ideal conductor r.

Proof §4 equations4.2 and following average good translation directions; convexity makes the translation parameter an interval. The determinant hypothesis is part of that actual mechanism. Our generic ideal character is not yet a rational character of a nonsingular quadratic form. At one split-prime ideal it acts on a linear residue coordinate; squaring that coordinate produces a degenerate quadratic form. This is a negative control against that direct substitution, not a global no-go for Burgess methods. Mapping, squarefree sieve and all source weights remain unpaid. Norm q_r, rational modulus q, radius B and row volume J cannot be identified by name alone.

## S1. Mapped source large sieve (conditional)

Pinned paper lines4707–4722, lemma sextic-large-sieve, allows arbitrary squarefree good column coefficients fixed independently of the evaluation row, with original zero extensions. Its squarefree row bracket is V+X+(VX)^(2/3). The source has a bounded prior audit in SEXTIC_SIEVE_BOUNDED_AUDIT.md; this use does not independently certify all its analytic dependencies.

Write F(v)=sum_(m~X) conjugate(chi_m(v)) sum_(n~X,(n,m)=1) c_nm chi_n(v). Fix m, apply Cauchy to the m-sum at cost O(X), use |chi_m(v)|<=1, then apply that sieve with coefficients c_nm. They include actual mu, Gauss and fixed external t/e phases. This yields

    sum_(v sf good,V<qv<=2V)|F(v)|²
      <=(VX)^eps X[V+X+(VX)^(2/3)] sum_nm|c_nm|².

This is a partial mapping to the actual two-column family, not cross-entry termwise estimation. Unit/S-sectors of a squarefree element row are finitely split; their character factors modify the fixed coefficients. Row-dependent profiles require the separation below, not silent absorption into c_nm.

## S2. Full conditional return — independently checked

Set X=L/qg. Keep the exact factor X/sqrt(q_n q_m) inside c_nm; it is bounded on both windows, so the outside prefactor is exactly Y/(LX), not an equality replacing q_k by X². On each row dyad V, separate the smooth function Phi(Y qv qt²/(qn qm)) together with both column windows by a common Fourier–Mellin expansion on three compact ratio intervals. The absolute expansion coefficients and required seminorms are bounded by C_A(1+V/J)^(-A), J=X²/(Y qt²); derivatives preserve this bound with fixed seminorms since Phi is Schwartz. Each Fourier factor in v has modulus one; the n,m factors remain row-independent. The actual coefficient square mass is O_W(X²).

Row Cauchy then gives amplitude, before Y/(LX), bounded by

    X^(3/2)[V+sqrt(VX)+V^(5/6)X^(1/3)](1+V/J)^(-A) times losses.

Summing dyads V>=constant gives the same expression with V=J for J>=1; for J<1 there is a rapid J^A tail. The original far frequency cutoff is removed only by the already-paid LINEAR Q9 CF15 bound, before this argument. No new squared-cutoff return is asserted.

Write J0=X²/Y; it is >=1 eventually and polynomial in U throughout the original ranges. Sum all integral t, dropping the poor selector only in the nonnegative upper envelope. The three row factors respectively sum to O(J0), O(sqrt(J0)log(2+J0)), and O(J0^(5/6)); the small-J tails have the same bounds. This uses exponents2,1,5/3 in the ideal sums and the rapid tail beyond q_t~sqrt(J0).

After Y/(LX), their costs for fixed g,a,d,e are respectively

    X^(5/2)/L,    sqrt(Y) X²/L times log,    Y^(1/6) X^(5/2)/L.

Now d<=O(U^(1/6)): the first term counts d, the second uses sum q_d^-3, the third sum q_d^-1 (logarithmic). The e|g factors are respectively1,q_e^-1/2,q_e^-1/6. The g-sums converge with exponents5/2,2,5/2 and their divisor factors. All original amplifiers cost O(P), including powers. Thus the independently checked conditional full envelope is

    |U_poor| <= P[U^(1/6)L^(3/2)+sqrt(U)L] times losses
                +H U^(-1+eps) times the original height factor.

The first term dominates on the original upper band. Its minimum deficit versus H U^(-1/200) is55243/75000, by the same affine endpoint calculation as Q9 with its exponent decreased by1/3. This improves the elementary Q8/Q9 fallbacks only under the source-sieve premise; the old conditional full moment remains stronger. No MB34/inverse/high gain follows. Independent q05_moment_audit returned conditional PASS for S1–S2: profile separation, finite unit/S sectors, coefficient mass, all small-J tails and outer sums. This checks the implication from the pinned sieve, not the source theorem itself. For clarity, the summed small-J tail before the outside prefactor is bounded by X^(3/2)(1+sqrt(X)+X^(1/3))*sqrt(J0), absorbed by the displayed main sums. The source ranges give X>=U^(r-.02), Y<=U and hence J0>=U^(1.2) eventually. No new source premise is certified.

## Search evidence and next discriminating action

Q09_CROSS_PRODUCT_ALIAS_RECEIPTS.json preserves four actual local shelf queries, all INCOMPLETE due to freshness; external search was deferred in those receipts. These are not absence certificates. The primary Heath-Brown candidate above was inspected separately and is not admitted as a supplier.

The next useful test must preserve the joint two-column arithmetic before Cauchy in m: that step incurs X in the squared norm and discards its phases. Removing this factor cannot be assumed, and arbitrary coefficient improvement is not the same as an estimate for the actual Mobius/Gauss coefficients. A next source-specific request must compare its complete return against the inherited stronger full-moment bound, not merely against this fallback. Q10 remains unsent.
