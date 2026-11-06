# Part 1 certificate and J1/J2 method

Scope: exact rational `ehat_N` for `N=10,20,50,100,200`, Arb intervals for
`N=500,1000,2000`, and judges J1/J2. This note does not cover the crossing
scan/core `H_N`, J3, or J4. Source formulas are pinned in `SOURCE_PINS.json`;
the preregistration was committed before this numerical run.

## Exact rational construction, N <= 200

For `K=ceil(N^(3/2))`, the script builds the upper Gram in the original
coordinates `(1,a_2,...,a_N)`:

```text
G_up = sum_{k=1}^{K-1} v_k v_k^T/[k(k+1)]
       + alpha q q^T + beta C_tilde,
alpha = 1/K + N/[K(K+1)],
beta  = 1/K + 2N^2/[K(K+1)],
q = (1,(n-1)/(2n)),
C[n,m] = (gcd(n,m)^2-1)/(12nm).
```

Every entry is an `fmpq`. To avoid `O(K N^2)` residue-row outer products,
each pair is split at the breakpoints of `floor(k/n)` and `floor(k/m)`. If
`a=n floor(k/n)`, `b=m floor(k/m)` on a block `L..R`, then

```text
sum (k-a)(k-b)/[k(k+1)]
  = (R-L+1) -(a+b+1)(H_R-H_{L-1})
    -(a+1)(b+1)(1/(R+1)-1/L).
```

The first coordinate uses the corresponding one-residue identity. A common
integer denominator `lcm(1,...,K)` scales the harmonic numbers, so each
block contribution is accumulated with integer arithmetic before a single
`fmpq` normalization per Gram entry. The exact Schur complement is then
computed by an `fmpq_mat` solve. Preflight independently replays the block
identity by direct exact sums and reproduces the source example
`ehat_3=2080069/11531604`.

The full Vasyunin Gram used for the old `e_N` was separately recomputed with
256-bit Arb enclosures. Each cotangent, logarithm, Euler constant, Gram entry,
linear solve, and resulting minimum is ball-arithmetic. The enclosed
`e_N` intervals reproduce the old Part A decimal estimates, while giving a
rigorous comparison for J1 at all exact-grid values. At `N=10,20,50`, the
Arb minimizer coefficients also enclose the true optimum used in the RHS of
(11), so J2 is evaluated at the actual optimum, not at the old float vector.

## Certified large-N intervals

At `N=500,1000,2000`, the floating segmented Gram is used only to choose a
candidate coefficient vector. The candidate's binary64 values are retained as
both `float.hex()` strings and exact dyadic rationals in
`certificate_witness_N*.json`. The candidate Gram itself is not used as a
premise in the interval proof.

For a fixed candidate `c`, the direct row loop computes the finite-head
objective `H` and half-gradient `g = Bc+d`. `b(c)`, `nu(c)`, `C c`, `alpha`,
and `beta` are then evaluated exactly as rationals using the Jordan divisor
factorization. This gives an interval for `U(c)` and for `g`. Since
`B >= beta C` and

```text
trace(C^-1) = 12 sum_{d=2}^N (1/J_2(d))
                     sum_{n|d, n>=2} n^2 mu(d/n)^2,
lambda_min(B) >= beta / trace(C^-1),
```

the Schur minimum is enclosed by

```text
U(c) - ||g||_2^2/lambda_min(B) <= ehat_N <= U(c).
```

The direct row evaluator uses `long double`; this host reports
`LDBL_MANT_DIG=53`, so the proof uses `u=2^-53`. It checks round-to-nearest,
finite inputs, finite residuals, and finite outputs. The script converts each
printed decimal center to an exact rational and adds an outward error allowance.
For `A=sum |a_n|`, `Rmax=1+A`, and `gamma_m=mu/(1-mu)`, the residual bound is

```text
delta_R <= gamma_(2N+2)(1+A) + 2u A + (2N+2) eta,
```

where `eta` is twice the printed `denorm_min`, covering its decimal conversion.
The objective and gradient allowances use `gamma_(8K+16)` to cover the row
operations, weighting, thread-local accumulation, and final reduction, plus
explicit additive subnormal and output-format allowances. These deliberately
conservative rational bounds and the resulting exact `||g||^2` upper bound
are recorded in each witness JSON. No transcendental library operation is
used in the direct evaluator; all `sqrt` operations in the final comparisons
are Arb-enclosed.

For the numeric J1 separation at large N, source equations (8)-(10) give the
Young slack

```text
U(c)-E(c) >= (sqrt(N)|b(c)| - N sqrt(nu(c)))^2/[K(K+1)].
```

Therefore the certified candidate upper bound for `e_N` is
`E(c) <= U(c)-slack`, and the recorded J1 margin is the certified lower
endpoint for `ehat_N` minus that candidate upper endpoint. The independent
all-input theorem `G_inf <= G_up` remains the main J1 proof.

## Results and interpretation

The CSV stores exact numerator/denominator pairs for the five rational values,
Arb enclosures for the true-Gram `e_N` at those values, and certified interval
endpoints for the three larger certificates. Ratios at every row are also
shown against the archived Part A `e_N` decimals; at large N these ratios are
explicitly diagnostic. The large-N CSV additionally gives a rigorous lower
bound on `ehat_N/e_N` but no finite upper bound for that ratio.

J1 passes analytically at all eight points and has strict numeric interval
separation at all eight. J2 passes at `N=10,20,50`; its `RHS - (ehat-e_N)`
intervals are strictly positive at the Arb-enclosed true optimizer. The
certificate threshold `ehat_N log N <= 1/2` is certified at all eight grid
points. Preregistered P1 is a MISS because the diagnostic ratios exceed 1.5
at `N=10,20,50`; P2 is a HIT.

These are finite certificate comparisons only. They do not establish
convergence of `ehat_N`, the bounded core assertion, Route B promotion, or RH.
