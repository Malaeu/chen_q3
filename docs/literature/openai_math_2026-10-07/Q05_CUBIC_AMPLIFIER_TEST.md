# Lower-degree amplification: exact quadratic-twist debt

2026-10-10, after Q4 f8c93534. Root and independent read-only q05_sieve_loss_map algebra/budget PASS. RH/SP/MB34 OPEN. No Q5 sent.

The source exponent5/6 comes from the sixth-power amplification H/P in paper.tex12343–12476, not directly from applying an arbitrary-coefficient sextic sieve. The source raw moment is conditional and applies with fixed arithmetic data and a common character nu. The question here is whether replacing a^6 by a^3 lowers the amplification cost while preserving that input.

## Exact test

Write psi_u(n)=nu(n)chi_n(u)^epsilon with zero extension. Let a be any good amplifier and define the quadratic character presentation theta_a(n)=chi_n(a)^(-3epsilon), also zero on nonunits. On columns coprime to a it is the inverse of chi_n(a)^(3epsilon); on the other columns it is zero. Then, for v=u a^3,

    nu(n) theta_a(n) chi_n(v)^epsilon
      = psi_u(n) 1_((n,a)=1).

This is an exact multiplicative identity including shared primes of u,a, not a new nonvanishing assertion. An existing fixed column mask a0 may be retained on both sides. Defining M_v^[nu theta_a] with this same masked presentation, squarefree-column separation gives

    M_u(L;W) = sum_(d|rad a) mu(d) psi_u(d)/sqrt(q_d)
                    M_(u a^3)^[nu theta_a](L/q_d;W).

If an original a0-mask is present, terms with (d,a0)!=1 vanish and the same a0-mask remains on the right. Both window rescaling and every zero are retained. The fact that theta_a is quadratic does not make it equal to1.

Choose Q=(H/U)^(1/3) and average over q_a<=Q. The usual divisor bound and scale supremum imply only

    sum_u |M_u(L)|^2
      << Q^epsilon / Q * sum_(a<=Q,u^(6)) sup_(L'<=L)
                       |M_(u a^3)^[nu theta_a](L')|^2.       C1

The image has q_v<<H. The map(u,a)->u a^3 has at most2^omega(v) admissible ideal factorizations: at each prime, k=e+3j with0<=e<=5 admits at most two j. At S, a is good and j=0. Units are recovered once a's chosen primary generator is fixed. Thus multiplicity costs only H^epsilon, but distinct a-labels can carry distinct theta_a. Counting image rows is not a bound on their labelled energies. In fact each labelled polynomial at scale L' is exactly the original u-polynomial with the a-mask at the same L'; only the full signed d-sum reconstructs the unmasked M_u(L). The new label is a faithful rewrite of masked energy, not an independent source of cancellation.

## Where the source estimate fails to supply the gain

Source raw-moment12348–12359 bounds a full v-ball for ONE fixed nu, then source scale-supremum12391–12406 bounds its common-profile supremum. In C1, nu theta_a varies with a; its good-prime conductor can grow with Q. Fixed-data constants do not provide uniformity in these twists.

Even grant, hypothetically, that the same raw estimate O(H U^epsilon) holds uniformly for EACH theta_a and original a0-mask. Freezing a and enlarging its u-image to the full v-ball then bounds the double sum by Q H U^epsilon. The factor1/Q in C1 cancels, leaving only H U^epsilon. Per-twist uniformity alone therefore does not give cubic amplification. A JOINT labelled-image estimate O(H U^epsilon) for the entire right-hand double sum is the missing input. No such estimate is derived here.

If that joint estimate were proved with the original masks/profiles/scale supremum, C1 would give H/Q=U^(1/3)H^(2/3), compared with the old H/P6=U^(1/6)H^(5/6), P6=(H/U)^(1/6). Their exponent difference is(log_U H-1)/6. This is a hypothetical budget, not a proved moment. At L=D the old per-row-family bound inserted before the a-sum costs Q*H/P6=H*P6 (up to small source losses); reducing it to H asks for about p=(log_U H-1)/6 saving. That is stronger than the original eta=1/200 deficit. Thus this test does not replace MB34 by the stronger joint premise. A new fixed-family theorem cannot be manufactured by calling a-dependent theta_a part of fixed nu.

## Search return and stopping condition

Three local dictionaries were run: Mobius coefficients/bilinear cubic character large sieve; multiplicative orthogonality/Katai/power-residue moments; signed Gram/Vaughan/sextic sieve. Each ask.sh --defer-external returned INCOMPLETE because semantic-index freshness failed; no absence claim. Previously inspected finite short-Mobius expansion E1–E4 already shows that freezing plain factors loses the needed coefficient cancellation. Q4's reciprocal contour retains the full unpaid MQ35. Neither is repeated here.

Negative control: a nontrivial quadratic theta_a changes relative phases of two columns, so dropping it cannot preserve a general squared polynomial. This is an algebraic control, not a counterexample to MB34 on the actual row family. Search hints, UNVERIFIED: jointly indexed quadratic-twist large sieve; vector-valued amplification with correlated conductor; labelled Gram sampling. Required return is C1 with actual theta_a and image, not a free arbitrary-coefficient or fixed-twist substitute.

Independent audit confirms the exact masked identity, multiplicity and per-twist QH cost; no new uniform twist estimate is supplied. Stop the naive cube entrance when only a fixed-twist raw estimate is available; the joint signed original problem remains open. No fixed-Hecke or P/M/R/K/high claim is upgraded.

Source locators independently confirmed: raw moment12353–12360; scale supremum12394–12408; sixth-power identity12416–12429; amplification12437–12449; fixed arithmetic data9250–9290. No status change to MB34, only exclusion of this direct lower-degree import.
