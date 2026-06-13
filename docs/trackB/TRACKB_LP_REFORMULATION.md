# Track B LP Reformulation

Status: SKETCH(LP formulation) plus OPEN(numerical dual witness not yet
solved).  This is Track B strategy/diagnostic documentation only: no Lean proof,
no Q3.Main change, no route mutation, and no RH-conditional input.

Atlas source:

```text
020 Cohn-Elkies LP framework
/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/020-cohn-elkies-lp.md
```

Unconditional input: the Cohn-Elkies LP/duality mechanism is
UNCONDITIONAL.  In this Track B use it is only a proof-transformation template:
any transferred witness still has to be checked inside the unconditional Weil
explicit-formula bookkeeping already used by Track B.

## Why This Exists

The price table currently has the right diagnosis but the wrong missing object:

```text
S5C0_SURCHARGE_CONFIRMED_MU_RATIO_OPEN
```

The missing number is not another scalar estimate.  It should be the LP gap
between the best admissible edge-defect direction and the best dual
magic-function clamp.  That is the Cohn-Elkies move:

```text
one dual witness + sign constraints + Fourier pairing = all configurations
clamped at once
```

For Track B, the word "configuration" means the finite K-cell packet cone.

## Primal

Fix K and the finite K-cell packet model used by the Track B scripts.  Let
`V_K` be the real finite coefficient space after the current `ker Q` boundary
conditions have been imposed.

The admissible cone is:

```text
C_K = {
  v in V_K :
    v is the coefficient vector of a finite Hermitian-square packet,
    Q_1(v) = Q_2(v) = 0                -- boundary / ker Q constraints,
    ||v||_G^2 = v^T G_K v = 1,
    support and bandlimit match the current K-cell receiver
}
```

Here `G_K` is the Gram / normalization matrix already implicit in the finite
operator probes, and the two `Q_i` are the same boundary functionals audited in
S1/S3.

Let `D_K` be the edge-defect matrix for the four-slot bookkeeping identity:

```text
Edge_K(v) =
  arch_K(v) - zero_PSD_K(v) + boundary_K(v) - prime_edge_K(v).
```

The sign convention is chosen so that positive `Edge_K` is the defect that has
to fit in the E5' budget.  Equivalently, if the local script emits the opposite
signed prime residual, replace `D_K` by `-D_K`; the LP definition is the
Rayleigh value of the chosen defect matrix, not a new mathematical object.

The primal value is:

```text
p_K = sup { v^T D_K v : v in C_K }.
```

In matrix form, after projecting to `ker Q` with basis `N_K`:

```text
G0_K = N_K^T G_K N_K
D0_K = N_K^T D_K N_K
p_K  = lambda_max(G0_K^(-1/2) D0_K G0_K^(-1/2))
```

This is exactly the finite "worst admissible direction" number Track B needs.
It is not a Selberg scalar-mask tax and it does not throw away the cone.

## Dual

The dual object is the Track B analogue of the Cohn-Elkies magic function.
Finite-dimensionally it is a clamp `lambda` plus a PSD slack matrix:

```text
lambda G0_K - D0_K = S_K
S_K >= 0.
```

The analytic/magic-function version of the same condition is:

```text
W_K(a) has the explicit-formula sign needed on the F2 margin,
hat W_K has the zero-side PSD / Hermitian-square sign,
W_K stays inside the same epsilon budget and boundary normalization,
Clamp(W_K) = lambda.
```

The Cohn-Elkies ratio `f(0)/f_hat(0)` becomes the finite clamp ratio:

```text
lambda = admissible upper bound for Edge_K(v) at ||v||_G=1.
```

Weak duality gives:

```text
Edge_K(v) <= lambda
```

for every admissible K-cell vector.  A feasible dual witness is therefore a
single certificate for all sampled directions, not another row-by-row ledger.

## `mu_budget(K)` As LP Gap

Define:

```text
d_K = inf {
  lambda :
    exists dual witness W_K / finite slack S_K
    satisfying the Track B sign, boundary, and PSD constraints
}
```

Then the LP budget exposed to the price table is:

```text
mu_budget_LP(K) = d_K - p_K.
```

This is a finite certificate gap, not a promise that the exact optimized
primal-dual gap stays positive.  If the relaxation is driven to strong-duality
equality and the guards consume the residual, then `mu_budget_usable(K)` is
zero and the LP route is a priced failure.

After numerical guards:

```text
mu_budget_usable(K) =
  d_K - p_K
  - closure_error_K
  - boundary_error_K
  - quadrature_error_K
  - finite_projection_error_K.
```

Gate:

```text
if mu_budget_usable(K) > 0:
  Route C has a computable budget margin at K.

if mu_budget_usable(K) <= 0:
  Route C is numerically/finitely fatal at K unless a stronger dual family is
  supplied.
```

This replaces the old open phrase "exact mu_budget(K) absent" by a concrete
object.  The formula is ready; the remaining open work is solving the dual
feasibility problem, measuring whether the certificate gap survives, and
attaching proof-grade error guards.

## Feasibility Protocol

Existing local instruments to reuse:

```text
scripts/trackb_edge_operator_probe.py clvgate
scripts/trackb_edge_operator_probe.py clvtaxpreflight
scripts/trackb_edge_operator_probe.py clvnegmass
scripts/trackb_edge_operator_probe.py liftsearch
q3.lean.aristotle/scripts/q3_psdpd_step13_pilot.py
```

Protocol:

1. Build the same finite K-cell packet space used in `clvgate`, including the
   `ker Q` projection and normalization matrix `G0_K`.
2. Extract or reconstruct the four-slot defect matrix `D0_K` from the same
   arch / zero / prime / boundary bookkeeping objects.  Do not introduce a
   new receiver.
3. Compute the primal Rayleigh value `p_K`.
4. Run a dual feasibility solve:

   ```text
   minimize lambda
   subject to lambda G0_K - D0_K >= 0
   plus sampled/interval sign constraints for the analytic witness W_K.
   ```

5. Record `d_K`, `p_K`, `d_K-p_K`, and all numerical guards.  The price-table
   number is `mu_budget_usable(K)`, not the raw Selberg tax.

A thin future wrapper may be useful, but it must be a wrapper around the current
K-cell matrices, not a new Track B object.  Until that wrapper exists, the LP
status is `COMPUTABLE_FORMULA_READY`, not `GREEN`.

## Failure Diagnostic

Card 020 says the invariant that must survive is the Fourier-self-dual pairing.
The Track B numerical test is:

```text
F2_SELF_DUAL_TEST(K, W_K):
  1. Check physical-side sign on the F2 margin.
  2. Check sampled Fourier / zero-side PSD sign.
  3. Check the same normalization is used by arch, prime, zero, and boundary
     slots.
  4. Re-run S3 closure with W_K inserted.
```

Failure statuses:

| failure | diagnostic number | meaning |
| --- | --- | --- |
| `LP_DUAL_NOT_PSD` | `min hat(W_K) < -tol` | The witness is not zero-side admissible. |
| `LP_DUAL_SIGN_WRONG` | margin sign violation | The witness does not clamp the edge defect. |
| `LP_DUAL_NORMALIZATION_BROKEN` | S3 closure fails after insertion | The explicit-formula transfer changed Q3 normalization. |
| `LP_GAP_NONPOSITIVE` | `d_K-p_K <= guards` | The LP route is priced and does not fit. |

This also explains S5C0: the surcharge was confirmed because PSD/nonnegative
Fourier sign is expensive.  `mu` stayed open because the finite LP dual gap was
not yet computed.

## Status Dictionary

```text
PROVED: none
SKETCH: primal/dual LP formulation and concrete mu_budget_LP(K) definition
OPEN: numerical dual witness solve; proof-grade continuous/interval guards
REFUTED: scalar-mask replacement for this LP budget
ZERO_CONSISTENT: S3 bookkeeping remains the regression gate
GAP: Fourier-self-dual survival of the actual dual witness W_K
```
