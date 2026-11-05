# Part A: analytic aggregation of the requested finite WLS

The object is R6 C (C1)–(C7), with **exact weights** `1/[k(k+1)]`; neither `1/k²` nor a finite head substituted for the full error is used. The isometry (C3) gives `Jr_n=ρ_n−ρ_1/n`, `ρ_n(x)={1/(nx)}`, and `b_n=log(n)/n`.

For the full normal matrix we use Vasyunin's autocorrelation identity: Báez-Duarte–Balazard–Landreau–Saias, arXiv:math/0306251v1, §9.1, Proposition 89; also Bettin–Conrey, arXiv:1111.0931, equation (13), p.12. These are separate from the BCF approximation paper arXiv:1211.5191.

For `g=gcd(n,m)`, `h=n/g`, `j=m/g`, `κ=log(2π)−γ_E`, define

```
V(h,j) = Σ_{a=1}^{j−1} {ha/j} cot(πa/j),  V(h,1)=0,
Q(n,m) = [κ(1/h+1/j)/2 + (j−h)log(h/j)/(2hj)
          −π(V(h,j)+V(j,h))/(2hj)]/g,
Γ(n,m) = Q(n,m)−Q(n,1)/m−Q(m,1)/n+κ/(nm).
```

This is the **infinite** weighted Gram, including its entire tail. `Γ(2,2)=log(2)/4`, and hence `e_2=1−log 2`. Native code caches coprime cotangent sums and pairs residues `a,j−a`; the computational cost remains O(N³), with cache reuse and parallel rows, not an asserted O(N²) method. Assembly uses long double, then the matrix and WLS solve use float64.

## Why the enormous K does not require a K-by-N allocation

The task's crude residual-tail budget can require trillions of rows. We aggregate the **finite K-row normal equations analytically**, with an explicitly bounded periodic correction. K is an integer cutoff, not a simulated number of rows or a timing claim.

Let `q_n=(n−1)/(2n)` and

```
M(n,m) = (n−1)(m−1)/(4nm) + (gcd(n,m)²−1)/(12nm).
```

These are the exact periodic means of `r_n` and `r_n r_m`. For any bounded P-periodic `f∈[0,1]`, a partial sum of `f−mean(f)` is bounded in absolute value by P. Abel summation therefore gives

```
Σ_{k>K} f(k)/[k(k+1)] = mean(f)/(K+1) + ε,
|ε| ≤ P/[(K+1)(K+2)].
```

Consequently, with `D=(K+1)(K+2)`, the finite WLS moments obey

```
Γ_K = Γ_∞ − M/(K+1) + error,  |error(n,m)| ≤ lcm(n,m)/D,
b_K = b_∞ − q/(K+1) + error,  |error(n)| ≤ n/D,
||v||²_{k≤K} = 1−1/(K+1) exactly.
```

The script actually solves these aggregated finite normal equations, and separately solves the full normal matrix. The `finite_WLS_estimate` is not the naïve full-Gram number relabelled as a row sum. The only approximation in this aggregation is the bounded periodic remainder plus stated point arithmetic.

For a candidate c put `T=Σ_{n=2}^N n|c_n|`. Its finite objective's aggregation error is at most `(2T+T²)/D`. The independently required omitted residual tail is at most

```
B_tail = (1+Σ|c_n|)²/(K+1).
```

We choose K at least `10^20` and at least `ceil[4000(1+||c||₁)²/e]`, then explicitly check `B_tail < 10^−3 e`. The large K is inexpensive precisely because normal moments, not K individual rows, are evaluated.

## Finite-optimum control rather than candidate-only control

The first N rows already have full column rank. For `f=Σc_n r_n`, writing `Δf(d)=f(d)−f(d−1)`, divisor inversion yields

```
c_n=−Σ_{d|n} μ(n/d)Δf(d), n≥2,
λ_min(Γ_K) ≥ λ0 = [4N(N+1)Σ_{n=2}^N τ(n)²]^−1, K≥N.
```

Here `|Δf(d)|≤2√[N(N+1)] ||f||_{first N rows}`; summing its divisor bound proves the floor. It uses no RH assumption.

For the exact full minimizer c, define `μ_R=1−2q·c+cᵀMc`. The exact identity

```
e_∞−e_K = Tail_R(c) + g_Kᵀ Γ_K^−1 g_K,
g_K=Γ_Kc−b_K
```

and the periodic estimates give a truncation-only upper bound

```
0 ≤ e_∞−e_K ≤ μ_R/(K+1)+(2T+T²)/D
  + λ0^−1 [||q−Mc||₂/(K+1)+||[2,…,N]||₂(1+T)/D]².
```

This is the CSV `finite_optimum_vs_infinite_bound`. The displayed bound uses the computed candidate in diagnostic arithmetic; full stationarity residuals, condition estimates, and arithmetic disagreement are reported separately. `finite_WLS_stationarity_gap_bound` also includes that numerical stationarity residual. These are **not outward-rounded interval certificates**. The asserted analytic truncation inequalities are distinct from numerical roundoff.

## Guards built before the grid run

- Exact `r_2` Gram and exact `e_2` checks.
- Independent periodic/digamma summation at `(2,3),(3,4),(6,10),(5,17)`, using period `lcm(n,m)` to sum the entire tail.
- J1/J2 predicates accept a valid toy input and reject deliberate violations before scientific output.
- J3 BCF identity checked directly; all prime powers are present in ψ.
- The float64 results at N≤200 are cross-checked with a separately assembled mpmath 30-digit matrix and solve.

Required BCF error in the main CSV is the **centered H error** `E(V_N−b_N)` from R7 B (7.9)–(7.12). A supplementary column records the uncentered global-H BCF error, which is a different object. The famous constant `2+γ_E−log(4π)` belongs to a conditional asymptotic for that uncentered polynomial under RH **and** the negative derivative-moment hypothesis H₋₁; it is not an unconditional prediction or an RH-only theorem. Burnol's bound is a lower bound, not a source of the missing upper rate.
