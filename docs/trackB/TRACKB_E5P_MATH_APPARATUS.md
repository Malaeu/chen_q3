# Track B E5p Mathematical Apparatus

Status: `PAPER_SPEC_AND_CROSSWALK_OBLIGATIONS_ONLY`.

This file is not a proof of E5p, not a Lean proof file, not a route mutation,
and not a claim that Q3 2025 `A3` has already supplied `mu_K`.

Core guard:

```text
Do not identify c_arch(K) with mu_K unless the operator/norm crosswalk is
proved.
```

Q3 2025 `A3` is the primary candidate source for the analytic `mu_K` budget.
It becomes spendable only after the crosswalk lemmas in Section 8 are proved.

---

## 0. Canon

Use `E5p` in filenames and task notes.  Read `E5p` as E five prime / E5-prime
/ E5 prime.  Avoid the ASCII-apostrophe spelling in tracked Track B files.

The current E5p obligations are named:

| Name | Meaning |
| --- | --- |
| `G-pos` | `G_K` is positive definite on `ker(Q_K)`. |
| `E-match` | The finite matrix `E_edge,K` is exactly the raw-edge ledger object. |
| `mu-normalization` | The analytic `mu_K` budget is proved in the same `G_K` units. |
| `tau-PSD-cert` | A penalty PSD certificate proves raw-edge domination on `ker(Q_K)`. |

Do not label these obligations with numbered A-style labels.  Q3 2025 already
uses `A3` for the Toeplitz bridge

```text
T_M[P_A] - T_P
```

with Arch margin, RKHS cap, and Szego-Boettcher discretization.

---

## 1. Budget Vocabulary

The Track B budget names are:

```text
E_edge,K = P_edge,K - P0_edge,K
```

`E_edge,K` is the raw edge defect.  Positive `E_edge,K` means the prime edge
exceeds the smooth edge baseline.

```text
certificate_gap_K = d_K - p_K - finite_guards_K
budget_slack_K    = mu_K - d_K - transfer_guards_K
```

`d_K - p_K` is not the analytic `mu_K` budget.  It is an internal finite
certificate gap or relaxation margin.  The external budget comparison is
`budget_slack_K`.

Old Step32F/LDL remains a certificate pattern only.  It is not a free pre-edge
reserve for E5p unless a same-unit ledger-support theorem separates a pre-edge
reserve.  Current default:

```text
m_old = 0
```

---

## 2. Coordinates And Weights

There are two coordinate systems:

```text
a  = raw log coordinate = r log p = log(p^r)
xi = a / (2*pi)
```

For prime powers `n = p^r`:

```text
xi_n = log n / (2*pi)
```

The Q3 2025 archive distinguishes:

```text
w_Q(n)    = 2 Lambda(n) / sqrt(n)
w_RKHS(n) =   Lambda(n) / sqrt(n)
```

The factor `2` is the evenization factor.  Any Track B comparison must prove
one of:

1. Track B uses `w_Q(n)` directly, or
2. Track B uses `w_RKHS(n)` and an evenization identity converts it to `w_Q(n)`
   on even test functions.

For a Track B raw-log cell:

```text
I_TB^a(K)  = [2K, 4K]
I_TB^xi(K) = [K/pi, 2K/pi]
```

Losing this `2*pi` conversion invalidates the bridge.

---

## 3. Finite Packet Space

For each active Track B cell `K`, fix a finite-dimensional real packet space:

```text
V_K = span{beta_{K,1}, ..., beta_{K,N_K}}.
```

A coefficient vector `c in R^{N_K}` represents:

```text
psi_c = sum_i c_i beta_{K,i}.
```

The Gram matrix is:

```text
(G_K)_{ij} = <beta_{K,i}, beta_{K,j}>_K
Norm_K(c) = c^T G_K c.
```

The `G-pos` obligation is:

```text
c != 0 and Q_K c = 0  ==>  c^T G_K c > 0.
```

Without this, `c^T G_K c` is not a norm on the boundary-null space.

---

## 4. Boundary Constraints

The boundary matrix is:

```text
Q_K : R^{N_K} -> R^{m_K}
ker(Q_K) = { c : Q_K c = 0 }.
```

The penalty trick uses the identity:

```text
c^T Q_K^T Q_K c = ||Q_K c||^2.
```

Therefore, on `ker(Q_K)`:

```text
c^T Q_K^T Q_K c = 0.
```

This is why a full-space PSD certificate with `tau_K Q_K^T Q_K` proves a
restricted inequality on `ker(Q_K)`.

---

## 5. Edge Matrices

Let `e_K(a)` be the packet evaluation vector in the chosen coordinate
convention.  The convention must be fixed once:

```text
a = log n
```

or

```text
xi = log n / (2*pi).
```

The prime edge matrix has the form:

```text
P_edge,K =
  sum_{n : log n in [2K,4K]}
    w(n) e_K(log n) e_K(log n)^T.
```

Here `w(n)` must be proved compatible with the Q3/Weil convention from
Section 2.

The smooth edge baseline has the form:

```text
P0_edge,K =
  int_{2K}^{4K} rho_edge,K(a) e_K(a) e_K(a)^T da.
```

The exact density `rho_edge,K` must be the one used by the E5p ledger.  Do not
replace this by an informal continuum approximation.

The finite raw edge defect is:

```text
E_edge,K = P_edge,K - P0_edge,K.
```

The target domination is:

```text
c^T E_edge,K c <= mu_K c^T G_K c
```

for every `c in ker(Q_K)`.

---

## 6. Analytic Weil Ledger

The Q3 functional is:

```text
Q(Phi) =
  int_R a_*(xi) Phi(xi) dxi
  - sum_{n>=2} w_Q(n) Phi(xi_n),
```

where:

```text
a_*(xi) = 2*pi*a(xi)
a(xi)   = log pi - Re psi(1/4 + i*pi*xi).
```

For a Track B packet vector `c`, one must construct a test function `Phi_c`
and prove a disjoint ledger:

```text
Q(Phi_c)
  = Safe_K(c)
    - Edge_true,K(c)
    - Tail_K(c)
    - Boundary_K(c).
```

The bridge from finite matrices to the analytic ledger is:

```text
Edge_true,K(c) = c^T E_edge,K c
```

or, with a paid model error:

```text
Edge_true,K(c)
  <= c^T E_edge,K c + edge_model_error_K c^T G_K c.
```

Without this lemma, a finite matrix certificate does not prove the analytic
E5p ledger statement.

---

## 7. Spendable Budget, Not Fake Budget

Never infer:

```text
c_arch(K) is large, therefore mu_K = c_arch(K).
```

The spendable budget must be computed after all transfers and already-spent
costs:

```text
mu_available,K =
  arch_reserve_K
  - discretization_loss_K
  - prime_cap_loss_K
  - tail_loss_K
  - boundary_loss_K
  - basis_transfer_loss_K
  - already_spent_cost_K.
```

Only after proving `mu_available,K >= 0` and the same-unit bridge may one set:

```text
mu_K := mu_available,K.
```

No double spending:

If Q3 2025 `A3` has already used a reserve to pay a full prime operator
including the edge prime support, that reserve cannot also be spent on
`E_edge,K`.  This is the same obstruction that blocks old Step32F/LDL from
being a free E5p reserve: the old prime block already contains edge support.

---

## 8. Q3 2025 A3 Candidate Source

Local source:

```text
/Users/emalam/Documents/GitHub/RH_2025_V3_October/Q3_paper/sections/
/Users/emalam/Documents/GitHub/RH_2025_V3_October/cert/bridge/
```

The Q3 2025 `A3` bridge supplies a candidate lower bound for:

```text
lambda_min(T_M[P_A] - T_P).
```

The archive uses the same basic node convention:

```text
xi_n = log n / (2*pi)
w_Q(n) = 2 Lambda(n) / sqrt(n).
```

The conservative proof-grade candidate margins from the lock JSON are:

| Q3 K | JSON | `c0` | `omega_condition_ok` | `barrier_ok` | `M_min` | `M_eval` |
| ---: | --- | ---: | --- | --- | ---: | ---: |
| 2 | `K2_A3_lock.json` | `0.9028668493703329` | true | true | 1 | 20 |
| 3 | `K3_A3_lock.json` | `0.9043681970359332` | true | true | 1 | 20 |
| 4 | `K4_A3_lock.json` | `0.9050660039059131` | true | true | 1 | 20 |

The larger raw floor values near `5.37` are not spendable Track B budgets.  In
particular:

| Q3 K | JSON | `c0` | `omega_condition_ok` | `M_min` | Verdict |
| ---: | --- | ---: | --- | ---: | --- |
| 2 | `K2_A3_floor.json` | `5.372183418997224` | true | 1 | candidate raw floor, still needs crosswalk |
| 3 | `K3_A3_floor.json` | `5.372183419225664` | false | 0 | `DEGENERATE_CERT_JSON` for proof use |
| 4 | `K4_A3_floor.json` | `5.372183419225667` | false | 0 | `DEGENERATE_CERT_JSON` for proof use |

Therefore the live candidate is:

```text
Q3 2025 A3 / lock c0 ~= 0.90
```

not:

```text
mu_K ~= 5.37.
```

Even the lock `c0` values are only candidate source evidence until the
crosswalk below is proved.

---

## 9. Crosswalk Lemmas

The crosswalk lemmas below are unrelated to the older `S5C0` tax route.  Here
`C0`--`C5` mean only the Q3-A3-to-Track-B normalization crosswalk.

### C0. Coordinate Crosswalk

For Track B cell `K_TB` and Q3 window `K_Q3`, prove:

```text
[K_TB/pi, 2K_TB/pi] subset [-K_Q3, K_Q3].
```

Equivalently:

```text
K_Q3 >= 2K_TB/pi.
```

Example:

```text
K_TB = 3.5  ==>  2K_TB/pi ~= 2.23,
```

so a Q3 window with `K_Q3=3` covers the Track B `K_TB=3.5` edge in frequency
coordinates.  Coverage is not enough; it only clears the coordinate gate.

Status: `GAP` until recorded as a theorem/ledger entry for the active K table.

### C1. Weight Crosswalk

Prove that the Track B finite edge matrix and the Q3 Weil functional use
compatible prime weights.

Allowed outcomes:

```text
Track B weight = w_Q(n) = 2 Lambda(n)/sqrt(n)
```

or:

```text
Track B weight = w_RKHS(n) = Lambda(n)/sqrt(n)
```

plus an evenization lemma:

```text
sum_{+/- xi_n} w_RKHS(n) Phi(+/- xi_n)
  = sum_{xi_n > 0} w_Q(n) Phi(xi_n)
```

for even `Phi`.

Status: `GAP` for Track B E5p until the exact finite backend convention is
matched to the Q3 convention.

### C2. Basis And Norm Crosswalk

Construct a linear map:

```text
J_K : V_K -> P_M,
```

where `P_M` is the Q3 2025 trigonometric-polynomial space used by the Toeplitz
bridge.  Prove constants `alpha_K, beta_K` such that:

```text
alpha_K c^T G_K c
  <= ||J_K c||_{L2(T)}^2
  <= beta_K c^T G_K c.
```

Best case:

```text
alpha_K = beta_K = 1.
```

Otherwise every Q3 Toeplitz budget must be scaled by `alpha_K` before it is
spendable in Track B `G_K` units.

Status: `GAP`.  This is the central operator/norm bridge.

### C3. Arch Reserve Transfer

Assume Q3 `A3` proves:

```text
<T_M[P_A] p, p> >= m_arch,K ||p||^2.
```

Apply `p = J_K c`.  With C2:

```text
<T_M[P_A] J_K c, J_K c>
  >= m_arch,K ||J_K c||^2
  >= alpha_K m_arch,K c^T G_K c.
```

Define:

```text
arch_reserve_K = alpha_K m_arch,K.
```

This is still not `mu_K`; it is only the Arch-side reserve in Track B units.

Status: `GAP` until `m_arch,K` is validated from Q3 `A3` lock data and C2 is
proved.

### C4. Prime/Smooth Ledger Extraction

The Q3 Toeplitz object is total:

```text
T_M[P_A] - T_P.
```

Track B needs the local edge defect:

```text
E_edge,K = P_edge,K - P0_edge,K.
```

Therefore prove a disjoint decomposition:

```text
<T_P J_K c, J_K c>
  = c^T P_edge,K c
    + Prime_rest_K(c)
    + Prime_tail_K(c),
```

and:

```text
<T_M[P_A] J_K c, J_K c>
  = c^T P0_edge,K c
    + Arch_rest_K(c)
    + Arch_tail_K(c)
    + Arch_reserve_K(c).
```

Then:

```text
<T_M[P_A] - T_P> on J_K c
  = - c^T E_edge,K c
    + nonedge terms
    + tails
    + reserve terms.
```

The signs and support partitions must be exact.  If `E_edge,K` is not the edge
piece of the Q3 Rayleigh ledger, Q3 `A3` does not prove the Track B E5p bridge.

Status: `GAP`.

### C5. No Double-Spending Budget Split

Define the spendable reserve:

```text
R_spend,K(c) =
  Arch_reserve_K(c)
  - NonEdgeCost_K(c)
  - TailCost_K(c)
  - BoundaryCost_K(c)
  - BasisTransferCost_K(c).
```

Prove:

```text
R_spend,K(c) >= mu_available,K c^T G_K c.
```

Then prove the threshold comparison:

```text
mu_available,K >= mu_cert,K + cert_guard_K.
```

This is the real same-unit bridge.  It must also prove that no reserve used in
Q3 `A3` has already paid the Track B edge support.

Status: `GAP`.

---

## 10. Same-Unit Bridge Theorem

The theorem to prove next is:

```text
Theorem Q3A3_crosswalk_to_TrackB_mu_K.
```

For each active Track B cell:

```text
K_TB in {2, 3, 3.5},
```

there exist a Q3 window `K_Q3`, a transfer map `J_K`, and constants:

```text
alpha_K,
m_arch,K,
Loss_nonedge,K,
Loss_tail,K,
Loss_boundary,K,
Loss_basis,K,
Loss_cert,K
```

such that:

1. Coordinate coverage:

   ```text
   [K_TB/pi, 2K_TB/pi] subset [-K_Q3, K_Q3].
   ```

2. Norm transfer:

   ```text
   ||J_K c||^2 >= alpha_K c^T G_K c.
   ```

3. Arch reserve:

   ```text
   <T_M[P_A] J_K c, J_K c> >= m_arch,K ||J_K c||^2.
   ```

4. Disjoint ledger:

   ```text
   The reserve used here has not already paid E_edge,K.
   ```

5. Spendable budget:

   ```text
   mu_available,K =
     alpha_K m_arch,K
     - Loss_nonedge,K
     - Loss_tail,K
     - Loss_boundary,K
     - Loss_basis,K
     - Loss_cert,K
   ```

   satisfies:

   ```text
   mu_available,K >= mu_cert,K.
   ```

Then:

```text
analytic mu_K >= mu_cert,K
```

in the same `G_K`-normalized raw-edge units.

This theorem is exactly where Q3 2025 `A3` / `c_arch(K)` may enter.  It cannot
enter as `mu_K` before C0--C5 are discharged.

---

## 11. Penalty PSD Certificate

For supplied finite thresholds:

```text
mu_cert,2   = 0.45
mu_cert,3   = 0.51
mu_cert,3.5 = 0.75
```

the current finite interval certificate has the receiver form:

```text
mu_cert,K G_K - E_edge,K + tau_K Q_K^T Q_K >= 0.
```

This proves, for every `c in ker(Q_K)`:

```text
c^T E_edge,K c <= mu_cert,K c^T G_K c.
```

Proof:

```text
0 <= c^T (mu_cert,K G_K - E_edge,K + tau_K Q_K^T Q_K) c
   = mu_cert,K c^T G_K c - c^T E_edge,K c
```

because `Q_K c = 0`.

This implication is clean.  It is not the current mathematical blocker.

Current finite certificate status:

```text
INTERVAL_CERT_PASS_FOR_SUPPLIED_MU
```

Not:

```text
E5P_BRIDGE_PASS
```

because `mu-normalization` is still open.

---

## 12. Main Edge Closure Theorem

The clean edge theorem is:

```text
Theorem E5pEdgeClosure_K.
```

Fix `K_TB in {2,3,3.5}` and Track B data:

```text
V_K, G_K, Q_K, E_edge,K.
```

Assume:

```text
(G-pos)
  G_K is positive definite on ker(Q_K).

(E-match)
  E_edge,K is exactly the raw edge defect in the E5p ledger,
  with the same sign, weights, coordinate, and packet basis.

(Mu-bridge)
  Q3A3_crosswalk_to_TrackB_mu_K proves
  mu_K >= mu_cert,K + guards_K
  in G_K-normalized raw-edge units.

(Penalty-cert)
  There exists tau_K >= 0 such that
  mu_cert,K G_K - E_edge,K + tau_K Q_K^T Q_K >= 0.
```

Then, for every `c in V_K` with `Q_K c = 0`:

```text
c^T E_edge,K c <= mu_K c^T G_K c.
```

Proof:

The penalty certificate gives:

```text
c^T E_edge,K c <= mu_cert,K c^T G_K c.
```

The same-unit bridge gives:

```text
mu_cert,K <= mu_K.
```

By `G-pos`, `c^T G_K c >= 0` on `ker(Q_K)`, hence:

```text
mu_cert,K c^T G_K c <= mu_K c^T G_K c.
```

Therefore:

```text
c^T E_edge,K c <= mu_K c^T G_K c.
```

The theorem is logically short; the work is in the obligations.

---

## 13. Local Ledger Closure Theorem

The edge theorem alone is not a full E5p ledger closure unless E5p is defined
only as local raw-edge domination.  For a local ledger closure, prove:

```text
Theorem E5pLocalLedger_K.
```

For every admissible packet vector `c in C_K cap ker(Q_K)`:

```text
Q(Phi_c)
  = Safe_K(c)
    - Edge_true,K(c)
    - Tail_K(c)
    - Boundary_K(c).
```

Assume constants `mu_K`, `tail_K`, `boundary_K`, and `final_slack_K` with:

```text
Safe_K(c) >=
  (mu_K + tail_K + boundary_K + final_slack_K) c^T G_K c.

Edge_true,K(c) <= mu_K c^T G_K c.

Tail_K(c) <= tail_K c^T G_K c.

Boundary_K(c) <= boundary_K c^T G_K c.

final_slack_K >= 0.
```

Then:

```text
Q(Phi_c) >= 0.
```

If Q3 `A3` is used to prove `Q(Phi_c) >= 0` directly, do not also split out
the same reserve and spend it again on the Track B edge theorem.  Choose one
ledger accounting path and keep it disjoint.

---

## 14. Current Proof Status

| Object | Status |
| --- | --- |
| Penalty implication on `ker(Q_K)` | `FORMAL_PATTERN` / mathematically clean. |
| Finite interval PSD for supplied `mu=(0.45,0.51,0.75)` | `INTERVAL_CERT_PASS_FOR_SUPPLIED_MU`. |
| Q3 2025 `A3` / `c_arch(K)` | `CANDIDATE_SOURCE`. |
| Same-unit bridge from Q3 `A3` to Track B `mu_K` | `E5P_BRIDGE_NORMALIZATION_GAP`. |
| Full E5p closure | `NO`. |

Do not summarize this state as "essentially closed."  The correct summary is:

```text
E5p reduces to the exact crosswalk obligations C0--C5 plus the finite
penalty certificate already available for supplied mu thresholds.
```

---

## 15. Next Proof-Producing Patch

Do not run another float search first.  Do not assert that `c_arch(K)` is
`mu_K`.

The next proof-producing patch is:

```text
Q3A3_CROSSWALK_TO_TRACKB_MU
```

Input:

```text
Q3 2025 A3 lock margin c0,
Track B K-cell data,
finite thresholds 0.45 / 0.51 / 0.75.
```

Output:

```text
mu_available,K in Track B G_K units.
```

Required checks:

| Check | Failure verdict if it fails |
| --- | --- |
| C0 coordinate coverage | `NORMALIZATION_GAP` |
| C1 weight crosswalk | `NORMALIZATION_GAP` |
| C2 basis/norm map | `KERNEL_OR_NORM_MISMATCH` |
| C3 arch reserve transfer | `NORMALIZATION_GAP` or `THRESHOLD_FAIL` |
| C4 prime/smooth ledger extraction | `LEDGER_EXTRACTION_GAP` |
| C5 no double-spend split | `DOUBLE_SPEND_GAP` |
| JSON validity (`M_min`, `M_eval`, `omega_condition_ok`) | `DEGENERATE_CERT_JSON` |

Possible final verdicts:

```text
E5P_BRIDGE_PASS
E5P_BRIDGE_THRESHOLD_FAIL
E5P_BRIDGE_NORMALIZATION_GAP
E5P_BRIDGE_KERNEL_MISMATCH
E5P_BRIDGE_LEDGER_EXTRACTION_GAP
E5P_BRIDGE_DOUBLE_SPEND_GAP
E5P_BRIDGE_DEGENERATE_CERT_JSON
```

Only `E5P_BRIDGE_PASS` permits promoting the supplied finite PSD certificate
to an E5p edge closure proof.

---

## 16. Lean Architecture

Lean should not recompute `c_arch`, Arb eigenvalues, integrals, or prime sums.

Lean should check compact proof objects:

1. Abstract penalty receiver theorem.
2. Matrix identity / LDL / interval-rational certificate payload.
3. Boundary-null vanishing:

   ```text
   Q_K c = 0 ==> c^T Q_K^T Q_K c = 0.
   ```

4. Final ledger theorem:

   ```text
   all inequalities hold ==> Q(Phi_c) >= 0.
   ```

The heavy numerics should be compressed into one of:

- exact rational LDL,
- weighted-square identity,
- interval certificate with rational enclosure,
- small independently checkable payload.

No Lean file should be edited for E5p until the paper crosswalk C0--C5 is
stable.
