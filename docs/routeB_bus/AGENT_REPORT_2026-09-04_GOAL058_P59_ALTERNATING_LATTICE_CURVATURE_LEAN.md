# Claude-agent report — Goal 058: P59 alternating lattice curvature (Lean)

Date: 2026-09-04
Task: `docs/Codex/TASK_2026-09-04_goal058_p59_alternating_lattice_curvature_lean.md`
Judge source: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_ALTERNATING_LATTICE_FORM_OF_THE_CURVATURE_WALL_2026-09-03.md`
(verdict `f788d2fa`, `REQ-2026-09-03-LATTICEWALL`; item 4 of the request carries the paper derivation)
Executor: Linux-Claude agent (Codex down); branch `rh_clean`, main checkout, **no commit, no push**
File: `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean` (740 lines)

```yaml
TASK_ID: GOAL058_P59_ALTERNATING_LATTICE_CURVATURE_LEAN
RESULT: COMPLETE
ITEMS_KERNEL_GREEN: [1, 2, 3, 4, 5, 6]
ITEMS_BLOCKED: []
RECORDED_GAP: P59_PROJECTIVE_NODE_INEQUALITY_NORMALIZATION_GAP   # item 6 denominator only; item 6 itself is proved
AXIOMS: [propext, Classical.choice, Quot.sound]
LEAN_EDIT_PERFORMED: true      # one new file only; no existing .lean file touched
NUMERICAL_RUN_PERFORMED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
HONESTY_STATE: CHALLENGER_NOT_RH
```

No existing `.lean` file was edited: every helper the judge's items needed (the additive
counterpart of `prod_erase_zero_Icc_symm`, the alternating `η(2)` value, the `1/n²`-weighted
Cauchy–Schwarz step) is proved locally in the new file.

## Validation — commands and exit codes

| where | command | exit |
|---|---|---|
| `q3.lean.aristotle` | `lake env lean Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean` | `0` |
| `q3.lean.aristotle` | `lake build Q3.Proofs.RouteB.Proposition59AlternatingLatticeCurvature` | `0` (`Build completed successfully (7775 jobs)`, module built in 37 s) |
| repo root | `scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean` | `0` (`q3_check ok`) |

Exit codes taken from `${PIPESTATUS[0]}` where the output was piped.
`grep -n "sorry\|admit\|axiom \|exact?"` over the file: **no match** (exit 1). No `axiom`
declaration, no `sorry`, no `admit`, no `exact?`. Nothing in the file is cofinal — every
statement is an identity or an inequality at a fixed `(L, N)`.

## `#print axioms` output (all 18 printed declarations)

```
'Q3.RouteB.hasSum_even_zeta_two'                          [propext, Classical.choice, Quot.sound]
'Q3.RouteB.hasSum_alternating_zeta_two'                   [propext, Classical.choice, Quot.sound]
'Q3.RouteB.hasSum_alternating_eta_two_zero'               [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59RawTransform_normalized_at_lattice' [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_normalizedSample_eq_ratio'       [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59AlternatingTailZetaTwo_hasSum'    [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_curvature_closed_form_real'      [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_alternating_curvature_identity'  [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_alternating_tail_abs_le'         [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_scaled_alternating_tail_abs_le'  [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_alternating_head_split'          [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_weighted_curvature_inequality'   [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_normalizedSampleZ_eq_ratio'      [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59ProjectiveDefect_eq_two_mul'      [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59SymmetricNodeError_eq'            [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_projective_node_inequality_row'  [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59RawTransform_norm_at_zero'        [propext, Classical.choice, Quot.sound]
'Q3.RouteB.proposition59_projective_node_inequality'      [propext, Classical.choice, Quot.sound]
```

Expected set exactly. `lake build` reprints the same list at module level.

## Per-item status

| item | judge's name | status | main declaration |
|---|---|---|---|
| 1 | alternating eta-two sum | KERNEL GREEN | `hasSum_alternating_eta_two_zero` |
| 2 | normalized P59 sample | KERNEL GREEN | `proposition59RawTransform_normalized_at_lattice` |
| 3 | alternating curvature identity | KERNEL GREEN | `proposition59_alternating_curvature_identity` |
| 4 | alternating tail bound | KERNEL GREEN | `proposition59_alternating_tail_abs_le`, `proposition59_scaled_alternating_tail_abs_le` |
| 5 | weighted curvature inequality | KERNEL GREEN | `proposition59_weighted_curvature_inequality` |
| 6 | projective weighted-node inequality | KERNEL GREEN (with a recorded normalization gap in the *denominator only*) | `proposition59_projective_node_inequality` |

### Item 1 — `alternating eta-two sum`

Mathlib fact used: **`hasSum_zeta_two`** (`Mathlib/NumberTheory/ZetaValues.lean:458`,
`HasSum (fun n : ℕ => 1/(n:ℝ)^2) (π^2/6)`). Mathlib v4.26.0 carries **no** alternating zeta
value (`η(2)`), so it is derived here, not imported. The derivation is the even/odd split
`(-1)^n = 2·[Even n] − 1` plus the `m ↦ 2m` reindexing of `hasSum_zeta_two` through
`Function.Injective.hasSum_iff`.

```lean
theorem hasSum_even_zeta_two :
    HasSum (fun n : ℕ => if Even n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) (Real.pi ^ 2 / 24)

theorem hasSum_alternating_zeta_two :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (n : ℝ) ^ 2) (-(Real.pi ^ 2 / 12))

theorem hasSum_alternating_eta_two_zero :
    HasSum (fun n : ℕ => (1 + 2 * (-1 : ℝ) ^ n) / (n : ℝ) ^ 2) 0
```

The `n = 0` summand is `3/0 = 0` in Lean, so the `HasSum` over all of `ℕ` *is* the judge's
sum over `n ≥ 1`; this is stated in the docstring rather than hidden in the coercion.

### Item 2 — `normalized P59 sample`

Built exactly on `proposition59RawTransform_at_lattice` (whose own proof runs through
`proposition59PoleKernel_at_lattice_sign`) and `proposition59RawTransform_at_zero_eq_sqrt`.
The `L^{-1/2}` normalisation cancels in the ratio — this is the one place where the `√L`
amplification is *not* visible, and it is why item 6 has to reintroduce it through `‖F_v(0)‖`.

```lean
theorem proposition59RawTransform_normalized_at_lattice
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℂ) (h0 : 0 ∈ S) (hv0 : v 0 ≠ 0)
    {j : ℤ} (hj : j ∈ S) :
    proposition59RawTransform L S v (proposition59Pole L j) /
        proposition59RawTransform L S v 0 =
      (j.negOnePow : ℂ) * v j / v 0

def proposition59NormalizedSample (v : ℤ → ℝ) (n : ℕ) : ℝ := (-1 : ℝ) ^ n * v (n : ℤ) / v 0

theorem proposition59_normalizedSample_eq_ratio
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℝ) (h0 : 0 ∈ S) (hv0 : v 0 ≠ 0)
    {n : ℕ} (hn : (n : ℤ) ∈ S) :
    proposition59RawTransform L S (fun k => (v k : ℂ)) (proposition59Pole L (n : ℤ)) /
        proposition59RawTransform L S (fun k => (v k : ℂ)) 0 =
      ((proposition59NormalizedSample v n : ℝ) : ℂ)
```

Signed-mode version (needed by item 6): `proposition59NormalizedSampleZ`,
`proposition59NormalizedSampleZ_natCast`, `proposition59_normalizedSampleZ_eq_ratio`.

### Item 3 — `alternating curvature identity`

```lean
def proposition59RealPole (L : ℝ) (n : ℕ) : ℝ := 2 * (n : ℝ) * Real.pi / L
theorem proposition59RealPole_ofReal (L : ℝ) (n : ℕ) :
    ((proposition59RealPole L n : ℝ) : ℂ) = proposition59Pole L (n : ℤ)

def proposition59AlternatingHeadZetaTwo (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ n / (n : ℝ) ^ 2
def proposition59AlternatingTailZetaTwo (N : ℕ) : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ (k + N + 1) / ((k : ℝ) + N + 1) ^ 2

theorem proposition59AlternatingTailZetaTwo_hasSum (N : ℕ) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ (k + N + 1) / ((k : ℝ) + N + 1) ^ 2)
      (-(Real.pi ^ 2 / 12) - proposition59AlternatingHeadZetaTwo N)

theorem proposition59_alternating_curvature_identity
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) (hv : ∀ k : ℤ, v (-k) = v k)
    (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun k => (v k : ℂ)))) :
    proposition59Curvature L N v =
      2 * ∑ n ∈ Finset.Icc 1 N,
          (-1 : ℝ) ^ n * (proposition59NormalizedSample v n - 1) / proposition59RealPole L n ^ 2
        - L ^ 2 / (2 * Real.pi ^ 2) * proposition59AlternatingTailZetaTwo N
```

Route: `proposition59_curvature_closed_form` (complex) → `proposition59_curvature_closed_form_real`
(by `Complex.ofReal_injective`) → `proposition59_curvature_closed_form_positive_modes`
(`κ = L²/24 + L²/(2π² v₀) ∑_{n≤N} v_n/n²`, using the even row and the local additive
`sum_erase_zero_Icc_symm`) → the alternating form, where item 1 supplies
`head + tail = −π²/12` and item 2 supplies `(-1)^n f(x_n) = v_n/v_0`.
The hypotheses (`hv`, `hv0`, `hzeros`) are the ones the closed form already needed; nothing new
is assumed.

### Item 4 — `alternating tail bound`

Mathlib fact used: **`alternating_series_error_bound`**
(`Mathlib/Analysis/SpecificLimits/Normed.lean:853`), at `n = 0`, on the antitone summable weights
`k ↦ 1/(k+N+1)²`; summability comes from the already-proved
`proposition59TailZetaTwo_hasSum`. The sign `(-1)^{N+1}` is factored out first, so no
sign case-split is needed.

```lean
theorem proposition59_alternating_tail_abs_le (N : ℕ) :
    |proposition59AlternatingTailZetaTwo N| ≤ 1 / ((N : ℝ) + 1) ^ 2

def proposition59ScaledAlternatingTail (L : ℝ) (N : ℕ) : ℝ :=
  L ^ 2 / (2 * Real.pi ^ 2) * proposition59AlternatingTailZetaTwo N

theorem proposition59_scaled_alternating_tail_abs_le (L : ℝ) (N : ℕ) :
    |proposition59ScaledAlternatingTail L N| ≤ L ^ 2 / (2 * Real.pi ^ 2 * ((N : ℝ) + 1) ^ 2)
```

### Item 5 — `weighted curvature inequality`

`f : ℝ → ℝ` is completely arbitrary — no continuity, no `C²`, no relation to `Ξ` is
assumed or used. The signed split is isolated as its own exact identity before any
inequality is taken, so the place where information is thrown away is explicit.

```lean
def proposition59LatticeError (v : ℤ → ℝ) (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : ℝ :=
  proposition59NormalizedSample v n - f (proposition59RealPole L n)

def proposition59WeightedLatticeError (v : ℤ → ℝ) (f : ℝ → ℝ) (L : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, |proposition59LatticeError v f L n| / (n : ℝ) ^ 2

def proposition59TrialHead (f : ℝ → ℝ) (L : ℝ) (N : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 N,
    (-1 : ℝ) ^ n * (f (proposition59RealPole L n) - 1) / proposition59RealPole L n ^ 2

theorem proposition59_alternating_head_split          -- exact, error term still signed
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) (f : ℝ → ℝ) :
    2 * ∑ n ∈ Finset.Icc 1 N,
        (-1 : ℝ) ^ n * (proposition59NormalizedSample v n - 1) / proposition59RealPole L n ^ 2 =
      proposition59TrialHead f L N +
        L ^ 2 / (2 * Real.pi ^ 2) *
          ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ n * proposition59LatticeError v f L n / (n : ℝ) ^ 2

theorem proposition59_weighted_curvature_inequality
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) (hv : ∀ k : ℤ, v (-k) = v k) (hv0 : v 0 ≠ 0)
    (hzeros : ZerosRealOn Set.univ
      (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun k => (v k : ℂ))))
    (f : ℝ → ℝ) :
    proposition59Curvature L N v ≤
      proposition59TrialHead f L N +
        L ^ 2 / (2 * Real.pi ^ 2) * proposition59WeightedLatticeError v f L N +
        |proposition59ScaledAlternatingTail L N|
```

This is the judge's Q1 `bound: kappa<=S_XI+L^2/(2*pi^2)*W+abs(T)` with `S_Ξ` replaced by
`S_f` for an arbitrary `f`. Instantiating `f := centeredXi/centeredXi 0` is a one-line
specialisation, but it is deliberately **not** written here, because nothing downstream is
proved about that `f` and writing it would suggest an identification we do not have.

### Item 6 — `projective weighted-node inequality`

The task ordered the exact statement to be derived from the sampling identity and
Cauchy–Schwarz, and the verdict's constant to be transcribed or the discrepancy recorded.
Both happened: the **constant `π²/√45` and the `√L` amplification are reproduced exactly**,
and the discrepancy is confined to the denominator (see the gap section).

Objects (all new, all in the project's own terms):

```lean
def proposition59AnchorOverlap (v q : ℤ → ℝ) : ℝ := v 0 / q 0            -- A
def proposition59ProjectiveResidual (v q : ℤ → ℝ) (k : ℤ) : ℝ :=          -- r_k = v_k − A q_k
  v k - proposition59AnchorOverlap v q * q k
def proposition59ProjectiveDefect (v q : ℤ → ℝ) (N : ℕ) : ℝ :=            -- p
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), proposition59ProjectiveResidual v q k ^ 2
def proposition59SymmetricNodeError (v q : ℤ → ℝ) (N : ℕ) : ℝ :=          -- W_ground_trial
  ∑ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0,
    |proposition59NormalizedSampleZ v k - proposition59NormalizedSampleZ q k| / (k : ℝ) ^ 2
```

Main statements:

```lean
theorem proposition59RawTransform_norm_at_zero
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (v : ℤ → ℝ) (h0 : 0 ∈ S) :
    ‖proposition59RawTransform L S (fun k => (v k : ℂ)) 0‖ = Real.sqrt L * |v 0|

theorem proposition59_projective_node_inequality_row
    (N : ℕ) (v q : ℤ → ℝ) (hv : ∀ k : ℤ, v (-k) = v k) (hq : ∀ k : ℤ, q (-k) = q k)
    (hv0 : v 0 ≠ 0) (hq0 : q 0 ≠ 0) :
    proposition59SymmetricNodeError v q N ≤
      Real.pi ^ 2 / Real.sqrt 45 * Real.sqrt (proposition59ProjectiveDefect v q N) / |v 0|

theorem proposition59_projective_node_inequality
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v q : ℤ → ℝ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hq : ∀ k : ℤ, q (-k) = q k)
    (hv0 : v 0 ≠ 0) (hq0 : q 0 ≠ 0) :
    proposition59SymmetricNodeError v q N ≤
      Real.pi ^ 2 / Real.sqrt 45 *
        Real.sqrt (L * proposition59ProjectiveDefect v q N) /
        ‖proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun j => (v j : ℂ)) 0‖
```

Why `√45` and not `√90`. Mathlib gives `∑_{n≥1} 1/n⁴ = π⁴/90` (`hasSum_zeta_four`), so the
one-sided Cauchy–Schwarz constant is `π²/√90`. Three exact bookkeeping facts turn that into
the judge's `π²/√45`:

* the node sum is over the **symmetric** window, and both `r` and the samples are even, so
  the left side is `2 ×` the one-sided sum (`proposition59SymmetricNodeError_eq`);
* the anchor node contributes **nothing** to the defect — `r₀ = v₀ − (v₀/q₀)q₀ = 0`
  (`proposition59ProjectiveResidual_zero`) — hence `p = 2 ∑_{n=1}^{N} r_n²` exactly
  (`proposition59ProjectiveDefect_eq_two_mul`), not merely `≤`;
* `2/√90 = √2/√45` (`sqrt_ninety_split`, `projective_constant`).

So `2 · (π²/√90) · √(p/2) = (π²/√45)·√p` — the judge's constant is reproduced with no slack
introduced anywhere. The `√L` enters only through the exact node normalisation
`‖F_v(0)‖ = √L·|v₀|`; there is no kernel supremum, in agreement with
`P_NODE_TRANSFER_EXACT_SQRT_L`.

Supporting private lemmas: `head_zeta_four_le` (partial sums of `hasSum_zeta_four`),
`sqrt_zeta_four_const` (`√(π⁴/90) = π²/√90`), `weighted_cauchy_schwarz`
(via `Real.sum_mul_le_sqrt_mul_sqrt`), `abs_cast_negOnePow` (via `Int.abs_negOnePow`).

## What could not be proved, and why

### `P59_PROJECTIVE_NODE_INEQUALITY_NORMALIZATION_GAP` — recorded, item 6 not blocked

The verdict's Q3 line is

```
W_ground_trial <= pi^2/(sqrt(45)*abs(centeredXi(0)))*abs(A)*sqrt(L*p)
```

and what is proved is

```
W_ground_trial <= pi^2/sqrt(45) * sqrt(L*p) / ‖F_v(0)‖ .
```

The numerator side (`π²/√45`, `√(L·p)`) transcribes exactly. Two things on the denominator
side do not, and neither can be repaired from anything in the Lean development:

1. **`|centeredXi(0)|/|A|` versus `‖F_v(0)‖`.** Substituting one for the other *is* the
   identification of the normalized ground transform with `Ξ` at the anchor. That is the
   verdict's own `NEW_ANALYTIC_WORK` (`P59_WEIGHTED_LATTICE_ERROR_SOURCE_BOUND`, Input A);
   it is not a theorem here, and asserting it would be exactly the cofinal-from-finite move
   the task forbids. `centeredXi` exists in `ClassicalXiInterface.lean`, so the temptation is
   real; the file does not touch it.
2. **The meaning of `A`.** The verdict's `A` is a *phase-aligned overlap* of the ground and
   trial rows. What the proof uses is the **anchor-aligned** scalar `A = v₀/q₀` — the unique
   scalar for which `F_v` and `A·F_q` agree at `z = 0`, i.e. the one that makes the residual
   vanish at the anchor node. The two coincide only if the rows are already normalised at the
   anchor; without the verdict spelling out its normalisation, they are different objects.
   The proved statement names its own scalar, so nothing is smuggled.

This is recorded verbatim in a `/-! ... -/` section at the end of the Lean file, so the gap
travels with the source and not only with this report. Item 6 is **green as stated**; the code
marks the transcription boundary, not a hole in the proof.

### Nothing else

Items 1–5 have no residual. In particular no cofinal claim is made anywhere: every theorem is
quantified over a fixed `(L, N)`, and the two limit-shaped statements in the file
(`hasSum_*`) are about the ordinary `ζ`/`η` series, not about the `k → ∞` family.

## Deviations from the task's fact list

* The judge's item 1 asks for "the alternating zeta value `η(2) = π²/12`" with the Mathlib
  fact named. **Mathlib v4.26.0 has no `η(2)`.** Named and used: `hasSum_zeta_two`; `η(2)` is
  derived in `hasSum_alternating_zeta_two` (even/odd split + `m ↦ 2m` reindexing).
* Item 4's remainder estimate is `alternating_series_error_bound`, which does exist in
  v4.26.0 — no hand-rolled pairing argument was needed.
* `prod_erase_zero_Icc_symm` in the bridge file is stated for `CommMonoid`, so it does not
  additivize; the additive twin `sum_erase_zero_Icc_symm` is proved locally (private) rather
  than by editing the bridge file.
* Report path: the task file names `CODEX_REPORT_2026-09-04_...`; the executing instruction
  named `AGENT_REPORT_2026-09-04_...`, and the executor is not Codex, so this file uses the
  latter.

## Registered state

`LEAN_EDIT_PERFORMED: true` (one new file), `NUMERICAL_RUN_PERFORMED: false`,
`ROUTE_PROMOTION: false`, `RH_CLAIM: false`, `PX_RH_CLAIM: NOT_MADE`,
`HONESTY_STATE: CHALLENGER_NOT_RH`. No commit, no push — the orchestrator commits.
