# Independent tail and finite-transfer paper audit

DIAGNOSTIC_NEVER_A_PROOF. **No `CCM_PHI_AUDIT_COUNTEREXAMPLE` found in the assigned tail scope.** Equations (6.1)–(6.4), the gamma5 argument, and the appendix remainder bounds pass the checks below. This is an independent paper audit plus exact algebra/scalar diagnostics, not the separate Arb matrix replay, a reproof of the imported Rosser theorem, or a promotion of route status. Input SHA256 is recorded in `tail_audit_checks.json`. This report does not independently adjudicate the leading-moment proof in §§2–5.

## Equation (6.1): factor eight and whole-zero payment

The exact physical column is

    e_j(z)=2 d_j z sin(zL/2)/(sqrt(L)(z²−ω_j²)).

Thus its squared norm has coefficient 4/L. If z=γ+iη, |η|≤1/2 and γ≥T>Ω, then |z|²≤γ²+1/4 and |sin(zL/2)|²=sin²(γL/2)+sinh²(ηL/2)≤cosh²(L/4). Exactly,

    |z²−ω²|²−(γ²−ω²)²=2η²(γ²+ω²)+η⁴≥0.

Multiplying by two pays the negative-height partner and gives exactly 8cosh²(L/4)/L in (6.1), without another multiplicity factor hidden in w. Every positive-height zero is counted with its own multiplicity in N. An off-line quartet has two positive-height entries; its combined real block has nuclear norm at most 4||e(z)||², which the two positive-height payments cover. The transpose in the signed complex rank-one block is not changed into a PSD conjugate Gram: its nuclear norm is still the product of the two Euclidean norms. Functional/reflection symmetry and real basis ensure these norms agree. This uses the standard zeta critical-strip confinement and conjugation/functional-equation symmetries; it would not automatically apply to a fabricated divisor outside that strip.

For each summand v(t)=(t²+1/4)/(t²−ω²)²,

    v′(t)=−2t(t²+ω²+1/2)/(t²−ω²)³<0  (t>Ω).

Hence w is decreasing and O(t⁻²), sufficient for the integrations below.

## Equations (6.2)–(6.3): boundary atoms and Rosser budget

Write D=N−M. With all height-T atoms in the tail,

    ∫_[T,∞) w dN=∫_T^∞ w M′dt−w(T)D(T−)−∫_T^∞ w′D dt.

The error bound |D(T−)|≤R*(T) follows by a left limit from the asserted count theorem and continuous M,R*. Since w′<0,

    error≤w(T)R*(T)+∫_T^∞(−w′)R*dt
         =2w(T)R*(T)+∫_T^∞wR*′dt.

This confirms the factor two in the boundary term. Replacing N(T−) by N(T) in this identity would lose boundary atoms; the verdict explicitly retains the correct convention. Absolute convergence follows from N(t)=O(t log t).

For u=log t, the derivative of R(t)/log t as a function of u is

    [.443(1−log u)−1.588]/u².

It is negative for u≥log T300>5.9. At T300 the ratio is .53864992148…<.55, so R*(t)=.55log t dominates uniformly on the required half-line. This monotonicity requires no zero list. The imported Rosser theorem, including its exact definition of N and endpoint convention, remains an explicit external THEOREM premise. The report has not independently retrieved or reproved that theorem.

The positive expansions for I,J follow from (1−ω²/t²)⁻²=Σ(k+1)(ω²/t²)^k and monotone convergence. Here ell=log(T/(2π))>0, so the stated positive upper estimates are valid. The exact remaining geometric mass is r^K[(K+1)/(1−r)+r/(1−r)²]. Using the total d=2m+1 with x_j≤r gives the printed loose remainders. These expressions should not be used unchanged at a cutoff with ell<0; this does not occur for the audited m300 cell. The numerical I,J,E intervals themselves are assigned to the parent's independent Arb replay.

## Zero-free gamma5: missing-premise check

For s=σ+it, 0≤σ≤1, |t|≤5,

    |s(s−1)|²=(σ²+t²)((1−σ)²+t²)≤26².

For x≥1,

    x^{σ/2−1}+x^{−(1+σ)/2}≤2.

Together with n²≥1+3(n−1), n≥1, this gives Θ(x)−1≤2e^(−πx)/(1−e^(−3π)). Applying absolute values in the displayed theta–Mellin formula yields exactly

    |xi(s)−1/2|≤26e^(−π)/(π(1−e^(−3π)))=.35766971628…<1/2.

The verdict omitted the intermediate x-power inequality, but it is elementary and valid on the whole rectangle; it is not an unpaid hypothesis. The theta representation, analytic continuation of xi, and the fact that nontrivial ζ zeros lie in the critical strip are the standard inherited premises. Therefore there are no nontrivial zeros with |γ|≤5, and σ=L+1/5 is a valid uniform critical-line simple-zero sampling cap. This does not assume RH or assert a numerical first zero.

## Finite head–tail transfer

Let H=A−R_T be the head. From ||R_T||1≤E, one has tr H≥a−E and ||H||F≤√q+E, because ||R_T||F≤||R_T||1. Thus

    4tr(H)/σ−||H||F²/σ² ≥4(a−E)/σ−(√q+E)²/σ²=F−.

This is valid for signed/indefinite tails. It does not require A or H PSD. Applying the imported exact head rank–trace consumer gives (6.4); that consumer and its same-source block normalization are explicit dependencies, not newly established by this tail audit. Replacing actual N by its integer upper bound185 weakens both requested lower bounds. Since M(T)+.55log T=185.3596…<186, integer N≤185 is valid; no erroneous floor-to184 occurs. Rational source gates yield F−=383.6937770627…, so ceiling produces14 and100. The finite trace correction is retained; raw2−v is not used.

## Appendix analytic remainders

For Re Z>0, the periodic-Bernoulli integral remainder after K terms gives |rψ|≤|B2K|/(2K(Re Z)^(2K)); differentiating that integral gives |rψ′|≤|B2K|/(Re Z)^(2K+1). The claimed bounds are therefore conservative for complex Z; no unproved real-positive alternating-series rule is applied to complex Z. The standard periodic Bernoulli supremum bound applies to even order2K. Shifting back through32 recurrence terms has the printed signs. Exact differentiation of f(w)=Imψ(1/4+iw/2)/(2w) gives the stated diagonal sum; its w=0 continuation is ψ′(1/4)/4. The mixed-index divided difference has the printed sign. Finally a²/[(a²+ωj²)(a²+ωk²)]≤1/a² gives the exponential remainder; increasing a and summing the geometric envelope gives the printed etail.

`tail_audit_checks.py` checks four exact algebraic identities and independently evaluates the gamma5 bound, Rosser ratio, and rational finite score at80 decimal digits. Five complex digamma/trigamma spot diagnostics fit inside the analytic EM remainder, with maximum error/bound about .01555. These spot checks support implementation checking only; the integral remainder derivation supplies the uniform justification. No zero list, new CCM matrix, eigensystem, route-state edit, or export was used.
