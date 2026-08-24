# TASK 2026-08-24 — selected Ferrers Abel–Poisson L2 lock

```yaml
task_id: H2A_4_1B_3C_1_12_SELECTED_FERRERS_ABEL_POISSON_L2_LOCK_LEAN
authorized_by: PROSHKA_VERDICT_REQ_2026_08_23_W_W3_DIRECTIVE_CONFLICT_RESOLUTION_2026-08-23.md
authorization_commit: 2fbd66907fe00fb2aee9517ec0607bfed57bd0a2
review_head: 9acd330072611a0335bedcce86f98bd14840ee82
preflight_blob: f90ea7b154e895e068cb11ca7105e19306709b90
governing_shape_commit: d4cd2e466f4b021485a407d1565ac9ee353e1083
mode: ONE_GOAL_ONE_COMMIT_LEAN_SOURCE_TRANSACTION
```

## Governing source

Read the full verdict before editing:

`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_23_W_W3_DIRECTIVE_CONFLICT_RESOLUTION_2026-08-23.md`

The verdict supersedes the concurrent read-only W3 stop while retaining its W2
admission. Its semantic repairs govern this task: the production packet may be
complex-valued; exact evenness, not real-valuedness, is load-bearing; endpoint
seams are removed only in the almost-everywhere or L2 category.

## Authorization boundary

```text
Lean source transaction: authorized
Numerics: forbidden
Aristotle: forbidden
Root-energy or cofinal-rate claims: forbidden
New paper axiom: forbidden
New sorry, admit, native_decide, axiom, or theorem weakening: forbidden
```

## Preflight

Before creating the Lean source, run `./ask.sh` for the exact existing theorem
names for packet evenness, zero mass, `dStar`/`I_m` measurability,
finite-support bounds, and circle Fourier APIs. Search the pinned Mathlib tree
with `rg` and typed `#check` probes. Do not reconstruct external declaration
names from memory.

## One target

Create:

`q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean`

Required public surface:

```lean
noncomputable def selectedFerrersReflectedAbel
    (k : ℕ) (r u : ℝ) : ℂ

noncomputable def selectedFerrersAbelLimit
    (k : ℕ) (u : ℝ) : ℂ

theorem selectedFerrersReflectedAbel_memLp
    (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
  MemLp (selectedFerrersReflectedAbel k r) 2
    (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k)))

theorem selectedFerrersAbelLimit_memLp (k : ℕ) :
  MemLp (selectedFerrersAbelLimit k) 2
    (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k)))

theorem selectedFerrersReflectedAbel_tendsto_L2 (k : ℕ) :
  Tendsto
    (fun r : ℝ =>
      ∫ u : ℝ,
        ‖selectedFerrersReflectedAbel k r u -
          selectedFerrersAbelLimit k u‖ ^ 2
        ∂(dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))))
    (𝓝[Set.Ioo (0 : ℝ) 1] 1)
    (𝓝 0)
```

## Proof order

1. Exact packet evenness.
2. Exact packet zero mass.
3. Finite periodization and its coefficient identity.
4. Local Poisson kernel nonnegativity and unit mass.
5. Exact reflected-Abel/Poisson-average identity.
6. Finite seam-set nullity.
7. Off-seam approximate-identity limit.
8. Fixed-`k` uniform translate bound and measurable, `r`-independent L2
   dominator.
9. Public L2 convergence theorem.

Compile the finite-periodization coefficient identity and local Poisson-kernel
convolution identity before attempting L2 convergence.

## Mandatory plants

```text
FULL_ENDPOINT_VS_MIDPOINT_ESTAR_SEAM_PLANT
ZERO_MASS_IS_LOAD_BEARING_PLANT
POINTWISE_WITHOUT_DOMINATION_DOES_NOT_GIVE_L2_PLANT
COMPLEX_EVEN_PACKET_DOES_NOT_REQUIRE_REAL_VALUEDNESS_PLANT
```

## Forbidden shortcuts

```text
continuous-source periodization theorem applied to the jumping packet
real-valuedness used in place of evenness
tsum at r = 1
production/full endpoint equality claimed at seams
pointwise convergence promoted to L2 without domination
fitted 2π or factor-two constants
Dirichlet–Jordan in the primary route
root-energy or cofinal-rate claims
```

## Source record

Write the transaction record at:

`docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_1_12_SELECTED_FERRERS_ABEL_POISSON_L2_2026-08-23.md`

```text
CLOSES: [W3_SELECTED_FERRERS_ABEL_REFLECTED_L2_LOCK]
OPENS: []
```

## Validation

From `q3.lean.aristotle`:

```bash
lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersAbelPoissonL2
```

From the repository root:

```bash
scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersAbelPoissonL2.lean
```

Every public theorem and every plant must have exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Failure codes

```text
W3_PACKET_EVENNESS_OR_ZERO_MASS_SOURCE_LOCK_GAP
W3_FINITE_PERIODIZATION_COEFFICIENT_GAP
W3_POISSON_KERNEL_LOCAL_API_GAP
W3_SEAM_AE_LIMIT_GAP
W3_L2_DOMINATION_GAP
W3_COMPLEX_PACKET_REALNESS_SURROGATE
```

Success token:

```text
W3_SELECTED_FERRERS_ABEL_POISSON_L2_LOCK_LEAN
```

Boundary:

```text
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```
