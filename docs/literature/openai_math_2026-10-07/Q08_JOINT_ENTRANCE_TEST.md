# Q8 joint entrance: restricted cubic Gram and explicit decompletion

2026-10-09. Independent q05_moment_audit G1/G2/D1/D2 PASS after explicit row-weight and a0 clarifications. RH/SP/MB34 OPEN.

The exact remaining object is Q8 QC18/19. Its quadratic character Q_k(v) is independent of the divisor m, but the cubic factor is not. Completing the frequency interval changes the object. Completing the column series also changes the object, but has an explicit inverse whose cost can be quantified.

Source: pinned quasiRH paper SHA256 42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3, corpus adc7f1241b42e322a6451854ab7e4b4c146bf78a. Local source lines575–584 define alpha and multiplicative primary generators; lines1676–1740 define completed reflection. The analytic reflection theorem itself remains an unverified source premise. Locator: Proposition `prop:completed-reflection`; its growth statement at1750–1752 allows constants to depend on L, Psi0, the moving prime set, its exponents, and the strip. Therefore uniformity in the moving primes is not supplied by that sentence. Source URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex

## G1. Exact complete cubic divisor Gram

Fix squarefree good k. For every oriented divisor m|k, n=k/m, set C_m(v)=chi_n(v)^2 conjugate(chi_m(v))^2, with zero extension modulo k. At each prime dividing k, this is one of the two nontrivial cubic characters; changing membership in m exchanges them. Thus distinct divisors give distinct characters on (O/k)^times. Character orthogonality gives

    sum_(v mod k) conjugate(C_m(v)) C_l(v) = phi(k) 1_(m=l).

The radial factor rho-tilde(Y q_v q_t²/q_k) remains a common v-dependent row weight; it is NOT part of c_m. G1 is unweighted complete-residue orthogonality only. All characters vanish on nonunits. Multiplication by the common Q_k(v) preserves this identity. For arbitrary fixed coefficients c_m (in particular the true Gauss, ray, two column-window and fixed-t factors),

    sum_(v mod k) |Q_k(v) sum_(m|k) c_m conjugate(C_m(v))|²
      = phi(k) sum_(m|k)|c_m|².

This remains true for the subset of divisors retained by both windows. If t meets k, every C_m(t) vanishes; otherwise those factors have modulus one. No cancellation between differing columns remains in this complete energy.

Replacing an l1 divisor bound by this l2 bound can improve its coefficient norm by at most sqrt(tau(k)). For every fixed epsilon>0 this is O_epsilon(q_k^epsilon). This comparison alone supplies no fixed power saving in U on q_k polynomial in U. It is not a bound for the actual signed QC18 and does not exclude a joint k,v argument.

## G2. Exact restricted matrix and negative control

For any finite actual row weight w(v), keep

    G_ml(w)=sum_(v squarefree elements) w(v) conjugate(C_m(v)) C_l(v).

For m!=l put r=product of primes whose membership in m and l differs. Their ratio is a primitive cubic character xi_(m,l) modulo r, times the necessary mask 1_((v,k/r)=1). Thus each off-diagonal entry is a genuine incomplete squarefree cubic character sum with that mask. For a nonnegative weight this is a positive Gram matrix; the actual transformed profile need not be nonnegative, so no positive-Gram substitution is licensed.

A singleton row v=1 has all C_m(1)=1; its matrix is all ones with eigenvalue equal to the number of retained columns. This negative control disproves inference of restricted orthogonality from complete orthogonality. It is not a counterexample to our radial family or its desired signed estimate. The two real windows, squarefree rows, units and outer signed sums remain required.

## D1. Exact completion inverse at compact support

For a fixed original twist Psi (including its zero mask), let A(b)=conjugate(alpha(b))^3 Psi(b)^3 on primary ideals coprime to the fixed E. It is completely multiplicative, including zeros. Put a0(n)=gamma_2(n) conjugate(alpha(n)), exactly as in the source. For fixed compact smooth V define

    D_X = sum_(n squarefree primary) a0(n) Psi(n)/sqrt(q_n) V(q_n/X),
    T_X = sum_b A(b)/q_b D_(X/q_b³).

Source entrance explicitly states: “No coprimality between the two variables in the following product is imposed” (lines1706–1707). The second expression is exactly the completed sum in source lines1724–1740; n and b may share primes. Ordinary Dirichlet convolution proves

    D_X = sum_b mu(b) A(b)/q_b T_(X/q_b³).

For fixed X both expansions are finite, since V has compact support away from infinity and q_n>=1. The coefficient at a combined b=c d is A(b)/q_b times sum_(c|b)mu(c), zero except b=1. No division by a zero-valued character occurs.

## D2. Conditional quantitative inverse, including small scales

If an independent argument established |T_x|<=C x^theta for EVERY x>0 with theta>0, and C uniform in all required moving arithmetic data, then

    |D_X| <= C X^theta sum_b q_b^(-1-3theta)
           <= C zeta_F(1+3theta) X^theta.

Here zeta_F is the Dedekind zeta function of Q(sqrt(-3)); its defining ideal series converges at this exponent. Thus this inverse does not automatically lose a power. Its constant depends on theta and cannot silently be called uniform as theta tends to zero. A bound for x>=1 alone requires separate payment for the small-scale part (or actual compact-support vanishing). The fixed E mask only reduces the absolute sum.

The same estimate holds for vectors in a fixed row Hilbert space: if A_u(b) acts by multiplication, its operator norm is at most one. Minkowski gives the same convergent ideal sum for ||D_X|| from a bound on ||T_x||, using the SAME nonnegative row measure for every x. A scale-dependent change of the row domain is not free. This does not turn the signed QC18 into a positive norm.

This is a conditional transfer, not a bound for T. Source lines1750ff allow growth constants to depend on moving prime data, so the needed uniform completed estimate cannot be read off from entireness. Nor does D1 apply verbatim to the fixed-k constrained divisor vector: its n-divisors, complementary m coefficients and two profiles need an exact map to a full completed column series. Both issues remain open.

## Alias return and next test

Three exact shelf dictionaries: common-conductor cubic divisor orthogonality; tensor-product character frames and restricted covariance; completed cubic reflection and inverse Euler factors. All three actual ask.sh runs returned INCOMPLETE (q3_docs freshness), external search deferred. No absence claim. Complete orthogonality and decompletion above are proved directly from their definitions, not inferred from a search hit.

Next decisive test: construct an exact completion of the two-column source before fixing k, preserving both profiles and all original zeros, then compute the complete reflected signed pairing and its moving-data cost. Stop if only fixed-twist entireness or complete-residue orthogonality is available; those are not QC19. No new Pro question yet.
