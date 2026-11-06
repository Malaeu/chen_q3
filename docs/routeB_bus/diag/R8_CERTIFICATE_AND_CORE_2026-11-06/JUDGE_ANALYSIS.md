# Judges: analytic specification before the production run

The task is pinned by SOURCE_PINS.json. Preregistration is commit
94ec9ac25 in the isolated worktree, delivered as 55ae4e1af on rh_clean before
production results. Independent analytic design was supplied by a read-only
Luna researcher, with no numerical runs. This note records its formulas.

## J4: literal plant, no prefix offset

Put L=log N, rho=5/6+7i, f(k)=2 Re(k^rho/rho),
and B_N(k)=psi(k)-k L s_N. Keep s_N unchanged, as in the task.
Then the planted head is exactly

    Hplant = Hhead - 2/L² sum B_N(k) f(k)/[k(k+1)]
                     + 1/L² sum f(k)²/[k(k+1)].

No f(1) subtraction, recentering, or integration constant is introduced.
In particular f(1)=2 Re(1/rho), not zero. If constructed from increments,
start with f(1), then add f(k)-f(k-1); starting at zero would introduce the
forbidden constant offset. Direct evaluation avoids this ambiguity entirely.

Writing a=2 Re(rho)-1=2/3, the planted self-energy satisfies

    P_N/L² = (108/1789) N^(2/3)/L²
      * [1 + cos(14 L - 2 atan(42/5) - atan(21))/sqrt(442)]
      + O(L^-2).

This follows by squaring f: the nonoscillatory term is
2 k^(5/3)/|rho|², and the oscillatory term is
2 Re(k^(2rho)/rho²). Dividing by k(k+1) and summing gives
2 N^a/(|rho|² a) and 2 Re(N^(a+14i)/(rho²(a+14i))),
respectively. The weight replacement error and integral-sum error are bounded
in N, hence O(L^-2) after division. This bounded asymptotic remainder is not
an artificial constant added to f.

The leading power is 2/3. The nonoscillatory local log slope is
2/3-2/log N; oscillations have relative amplitude 1/sqrt(442).
The exact discrete self-energy, evaluated on the same finite fitting grid,
is the preregistered slope reference. The full planted head also contains the
baseline and cross term, so dominance must be checked numerically, not assumed.
The preregistered gate is absolute fitted-slope difference <=0.05 on
[10^5,10^7], plus the direct prefix/no-offset check. Report both raw slopes
and slopes after multiplication by log² N. This tests the finite experiment;
it does not prove an asymptotic law for the original arithmetic residual.

## J3: exact tail versus paid bound

H=sum_{1<=k<K} R(k)²/[k(k+1)] and the exact omitted tail is
T=sum_{k>=K} R(k)²/[k(k+1)]. Thus E-H=T exactly.
Neither b²/K nor 5/log² N is T. The source states only

    |E-H-b²/K| <= 5/log² N.

Subtracting the bound as an equality would test a false statement. J3's
reproducible finite normalization gate compares independent direct remainder
rows against head plus the full floor-block shoulder at all N=3..200,
tolerance 1e-10. Any additional full-norm/tail check is reported separately;
this finite check alone is not represented as a direct computation of the
infinite tail. The off-by-one boundary is k=K for the tail.

## J1 and J2

Ginf <= Gup is an all-coefficient implication of source (8)-(12), not an
identity of numerical approximations. The exact rational construction is
checked at small N; rigorous numerical endpoints, when claimed, must be
outward-rounded. Reused e_N decimal estimates are diagnostic unless enclosed
by a new rigorous calculation.

For the true optimum a*, ehat <= U(1,a*) and e=E(1,a*), hence

    0 <= ehat-e <= U(1,a*)-E(1,a*)
       <= 2 [N |b(1,a*)|² + 2 N² nu(a*)]/[K(K+1)].

Thus (11) does apply to optimal coefficients. A float vector approximating a*
is not itself a certified exact optimum; the distinction must remain explicit.
