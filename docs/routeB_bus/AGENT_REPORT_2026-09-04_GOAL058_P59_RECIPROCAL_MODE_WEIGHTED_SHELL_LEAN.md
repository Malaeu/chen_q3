# Claude-agent report — Goal 058: P59 reciprocal-mode weighted `L²` shell (Lean)

Date: 2026-09-04
Judge source: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SHELL_SEARCH_SOURCE_TO_LATTICE_ATOM_2026-09-03.md`
(`§Q1 H1` = `P59_RECIPROCAL_MODE_WEIGHTED_L2_SHELL`, `§Q1 H3` = `P59_FULL_LATTICE_SUP_SHELL`,
`§Q2`, `§TOP_SHELL_CONSEQUENCES`)
Convention: `docs/routeB_bus/CONVENTION_CARD_GOAL058.md` — `Δ_n` in **FULL** ratios,
`R = diag(1/n)`, `x_n = 2πn/L`
Executor: Linux-Claude agent; branch `rh_clean`, main checkout, **no commit, no push**
File: `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ReciprocalModeWeightedShell.lean` (277 lines)

```yaml
TASK_ID: GOAL058_P59_RECIPROCAL_MODE_WEIGHTED_SHELL_LEAN
RESULT: COMPLETE
ITEMS_KERNEL_GREEN: [1, 2, 3, 4]
ITEMS_BLOCKED: []
AXIOMS: [propext, Classical.choice, Quot.sound]
LEAN_EDIT_PERFORMED: true      # one new file only; no existing .lean file touched
NUMERICAL_RUN_PERFORMED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
HONESTY_STATE: CHALLENGER_NOT_RH
OPEN_INPUT_NOT_SUPPLIED: P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND
```

No existing `.lean` file was edited. Nothing outside the new `.lean` file and this report
was written; `docs/cartographer/TOOLS.yaml` untouched.

## Validation — commands and exit codes

| where | command | exit |
|---|---|---|
| `q3.lean.aristotle` | `lake env lean Q3/Proofs/RouteB/Proposition59ReciprocalModeWeightedShell.lean` | `0` |
| `q3.lean.aristotle` | `lake build Q3.Proofs.RouteB.Proposition59ReciprocalModeWeightedShell` | `0` (`Build completed successfully (7776 jobs)`, module built in 15 s, 21 s wall) |
| repo root | `scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59ReciprocalModeWeightedShell.lean` | `0` (`q3_check ok`) |

Exit codes taken from `${PIPESTATUS[0]}` (all three commands were piped through `tail`).
`grep -n "sorry\|admit\|axiom \|exact?"` over the file: **no match** (grep exit `1`).
No `axiom` declaration, no `sorry`, no `admit`, no `exact?`, no `native_decide`.
`lake env lean` emits **no** warnings — the full output is exactly the six `#print axioms`
lines below.

Toolchain: `leanprover/lean4:v4.26.0`, Mathlib `v4.26.0`.

## `#print axioms` output (all six printed declarations)

```
'Q3.RouteB.proposition59WeightedLatticeError_eq_reciprocal' [propext, Classical.choice, Quot.sound]
'Q3.RouteB.reciprocal_energy_to_weighted_error'             [propext, Classical.choice, Quot.sound]
'Q3.RouteB.reciprocal_energy_to_node_sup'                   [propext, Classical.choice, Quot.sound]
'Q3.RouteB.reciprocal_energy_to_node_sup_at_radius'         [propext, Classical.choice, Quot.sound]
'Q3.RouteB.sup_error_to_weighted_error'                     [propext, Classical.choice, Quot.sound]
'Q3.RouteB.reciprocal_energy_to_curvature_bound'            [propext, Classical.choice, Quot.sound]
```

Expected set exactly. `lake build` reprints the same list at module level.

## Definitions introduced

```lean
def proposition59ReciprocalEnergySq (Δ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, Δ n ^ 2 / (n : ℝ) ^ 2

def proposition59ReciprocalWeightedError (Δ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, |Δ n| / (n : ℝ) ^ 2
```

`proposition59ReciprocalEnergySq` is the judge's `E_k² = ‖R_k Δ_k‖²` with `R = diag(1/n)`
(`|Δ_n|² = Δ_n²` for the real row). `proposition59ReciprocalWeightedError` is the judge's
`W_k` for an arbitrary real row.

Bridge to the existing development (proved by `rfl`, no new content):

```lean
theorem proposition59WeightedLatticeError_eq_reciprocal
    (v : ℤ → ℝ) (f : ℝ → ℝ) (L : ℝ) (N : ℕ) :
    proposition59WeightedLatticeError v f L N =
      proposition59ReciprocalWeightedError (proposition59LatticeError v f L) N
```

`proposition59LatticeError v f L n = F_v(x_n)/F_v(0) − f(x_n)` and
`proposition59WeightedLatticeError` are the objects of
`Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean`; this is why item 4 below
composes with `proposition59_weighted_curvature_inequality` verbatim.

Two private helpers: `head_zeta_two_le` (`∑_{n=1}^{N} 1/n² ≤ π²/6`, from Mathlib's
`hasSum_zeta_two` via `sum_le_hasSum`) and the constants
`sqrt_zeta_two_const : √(π²/6) = π/√6`, `sqrt_energy_const : √(C/L⁴) = √C/L²` (`0 ≤ C`, `0 < L`).

## Per-item status

| item | judge's line | status | declaration |
|---|---|---|---|
| 1 | `TOP_SHELL_CONSEQUENCES.NORMALITY_WEIGHT`, H1 first line | KERNEL GREEN | `reciprocal_energy_to_weighted_error` |
| 2 | `TOP_SHELL_CONSEQUENCES.IDENTIFICATION`, H1 second line | KERNEL GREEN | `reciprocal_energy_to_node_sup`, `reciprocal_energy_to_node_sup_at_radius` |
| 3 | H3 `P59_FULL_LATTICE_SUP_SHELL` | KERNEL GREEN | `sup_error_to_weighted_error` |
| 4 | composition with item 5 of verdict `f788d2fa` | KERNEL GREEN | `reciprocal_energy_to_curvature_bound` |

### Item 1 — `W ≤ (π/√6)·√C/L²`

```lean
theorem reciprocal_energy_to_weighted_error
    (Δ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hE : proposition59ReciprocalEnergySq Δ N ≤ C / L ^ 4) :
    proposition59ReciprocalWeightedError Δ N ≤
      Real.pi / Real.sqrt 6 * Real.sqrt C / L ^ 2
```

Mechanism exactly as the judge writes it: Cauchy–Schwarz
(`Real.sum_mul_le_sqrt_mul_sqrt`, `Mathlib/Data/Real/Sqrt.lean:464`) on the split
`|Δ_n|/n² = (1/n)·(|Δ_n|/n)`, then the Basel head `∑_{n≤N} 1/n² ≤ π²/6`
(`hasSum_zeta_two`, the finite partial-sum bound — no tail is summed) and
`√(C/L⁴) = √C/L²`. The constant is the judge's `π√C/(√6 L²)` on the nose.

### Item 2 — the node bounds

```lean
theorem reciprocal_energy_to_node_sup
    (Δ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hE : proposition59ReciprocalEnergySq Δ N ≤ C / L ^ 4)
    {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    |Δ n| ≤ (n : ℝ) * Real.sqrt C / L ^ 2

theorem reciprocal_energy_to_node_sup_at_radius
    (Δ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) {C L X : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hX : 0 < X)
    (hE : proposition59ReciprocalEnergySq Δ N ≤ C / L ^ 4)
    {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N)
    (hnX : (n : ℝ) ≤ X * L / (2 * Real.pi)) :
    |Δ n| ≤ X * Real.sqrt C / (2 * Real.pi * L)
```

`Finset.single_le_sum` gives `Δ_n²/n² ≤ E²`, hence `|Δ_n|/n ≤ √C/L²`, i.e. the judge's
`|Δ_n| ≤ n·E`. The radius form is the same bound at `n ≤ X·L/(2π)`, giving the judge's
`X√C/(2π L)` exactly.

The **`sup` is written as the pointwise family it is** — no `iSup` object is introduced, so
no `Nonempty`/`BddAbove` side condition is smuggled in.

### Item 3 — H3 `sup ⟹ W`

```lean
theorem sup_error_to_weighted_error
    (Δ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hsup : ∀ n : ℕ, 1 ≤ n → n ≤ N → |Δ n| ≤ C / L ^ 2) :
    proposition59ReciprocalWeightedError Δ N ≤ Real.pi ^ 2 / 6 * (C / L ^ 2)
```

Termwise `|Δ_n|/n² ≤ (C/L²)/n²`, then the same Basel head. Constant `π²/6` as the judge writes.

### Item 4 — composition with the alternating curvature inequality

The existing hypotheses of `proposition59_weighted_curvature_inequality`
(`Proposition59AlternatingLatticeCurvature.lean:398`) were transcribed, not guessed:
`hL : 0 < L`, `N`, `v : ℤ → ℝ`, `hv : ∀ k, v (-k) = v k`, `hv0 : v 0 ≠ 0`, the real-zeros
hypothesis `hzeros` on the window transform, and the comparison profile `f`.

```lean
theorem reciprocal_energy_to_curvature_bound
    {L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 1 ≤ N) (v : ℤ → ℝ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun k => (v k : ℂ))))
    (f : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hE : proposition59ReciprocalEnergySq (proposition59LatticeError v f L) N ≤
      C / L ^ 4) :
    proposition59Curvature L N v ≤
      proposition59TrialHead f L N +
        L ^ 2 / (2 * Real.pi ^ 2) * (Real.pi / Real.sqrt 6 * Real.sqrt C / L ^ 2) +
        |proposition59ScaledAlternatingTail L N|
```

i.e. `κ_F ≤ S_f + (L²/(2π²))·(π/√6)·√C/L² + |T|`, the requested shape, with the
weighted-error slot of the curvature inequality closed by item 1 and **no free error
functional left**. The `(L²/(2π²))·(√C/L²)` product is deliberately **not** cancelled in the
statement, so that the two factors stay readable against the verdict.

## What is open, and what is deliberately not claimed

- The shell's single open input — `P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND`,
  `∑_{n=1}^{N_k} |(-1)^n ξ_{k,n}/ξ_{k,0} − centeredXi(x_{k,n})/centeredXi(0)|²/n² ≤ C/L_k⁴`
  (verdict `§Q2`) — is **not** proved and **not** assumed as an axiom. It enters every
  theorem as an explicit hypothesis `hE` on an **arbitrary real sequence** `Δ : ℕ → ℝ`.
  Nothing in the file mentions `centeredXi` or any property of `Ξ`.
- Nothing is cofinal: every statement is an inequality at a fixed `(L, N)`. The judge's
  `COVERAGE_GUARD` `N_k/L_k → ∞` and the `→ 0` of the IDENTIFICATION line are statements
  about a family of cells and are not derived from the finite inequalities. The
  finite-cell inequality is the whole content a fixed cell can carry.
- `sup_error_to_weighted_error` is the H3 **implication only**; H3's own sup-rate
  `sup_{n≤N}|Δ_n| ≤ C/L²` remains open (the judge's H3 "first failure": probe 9 supports it
  only on finitely many cells).
- The verdict's normalization gap recorded by the previous agent
  (`P59_PROJECTIVE_NODE_INEQUALITY_NORMALIZATION_GAP`, item 6 denominator) is untouched and
  not used here.
- `hN : 1 ≤ N` is carried in every statement as the task specifies; the proofs do not need
  it (the `N = 0` cases are the empty sum), so `linter.unusedVariables` is switched off in
  the file header along with `linter.mathlibStandardSet` (matching the sibling file).

## Mathlib facts used

| fact | location |
|---|---|
| `Real.sum_mul_le_sqrt_mul_sqrt` (finset Cauchy–Schwarz) | `Mathlib/Data/Real/Sqrt.lean:464` |
| `hasSum_zeta_two` (`∑ 1/n² = π²/6`) | `Mathlib/NumberTheory/ZetaValues.lean` |
| `sum_le_hasSum`, `Finset.single_le_sum`, `Finset.sum_le_sum` | Mathlib order/topology basics |
| `Real.sqrt_div`, `Real.sqrt_sq`, `Real.sqrt_sq_eq_abs`, `Real.sqrt_le_sqrt` | `Mathlib/Data/Real/Sqrt.lean` |
| `div_le_div_iff₀`, `div_mul_cancel₀`, `mul_le_mul*` | `Mathlib/Algebra/Order/...` |

Note for future agents: in Mathlib v4.26 the unprimed `div_le_div_iff` is **gone**; the
name is `div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a/b ≤ c/d ↔ a*d ≤ c*b`
(`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:1364`).
