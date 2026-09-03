import Q3.Proofs.RouteB.Proposition59AlternatingLatticeCurvature

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

/-!
# Proposition 5.9 — the reciprocal-mode weighted `L²` shell

Judge verdict `PROSHKA_VERDICT_GOAL058_SHELL_SEARCH_SOURCE_TO_LATTICE_ATOM_2026-09-03`,
top shell `P59_RECIPROCAL_MODE_WEIGHTED_L2_SHELL` (H1) together with
`P59_FULL_LATTICE_SUP_SHELL` (H3).

The judge's H1 reads: with `Δ_n` the lattice error and

```
E² = ∑_{n=1}^{N} |Δ_n|² / n²        (the reciprocal-mode energy, `R = diag(1/n)`)
```

the hypothesis `E² ≤ C/L⁴` implies

* NORMALITY WEIGHT: `W = ∑_{n=1}^{N} |Δ_n|/n² ≤ (π/√6)·√C/L²`,
* IDENTIFICATION: `sup_{1 ≤ n ≤ X·L/(2π)} |Δ_n| ≤ X·√C/(2π·L)` for every `X > 0`.

H3 reads: `sup_{1 ≤ n ≤ N} |Δ_n| ≤ C/L²` implies `W ≤ (π²/6)·C/L²`.

**What this file is and is not.**  Everything below is the *implication* part of the
shell only — the finite-`(L, N)` Cauchy–Schwarz / single-term bookkeeping that the
verdict itself files under "classical".  The shell's single open input,
`P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND`
(`∑ |Δ_{k,n}|²/n² ≤ C/L_k⁴` for the actual ground family against the classical `Ξ`
samples), is **not** proved, not assumed as an axiom, and not stated about `Ξ`: it
enters every theorem below as an explicit hypothesis on an arbitrary real sequence
`Δ : ℕ → ℝ`.  Nothing here is cofinal in `k`, no property of `centeredXi` is used, and
no coverage guard `N_k/L_k → ∞` is claimed.

The convention card `docs/routeB_bus/CONVENTION_CARD_GOAL058.md` fixes `Δ_n` in FULL
ratios; `proposition59LatticeError` of
`Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean` is exactly that object
(`Δ_n = F(x_n)/F(0) − f(x_n)` at the node `x_n = 2πn/L`), which is why item 4 below
composes verbatim with `proposition59_weighted_curvature_inequality`.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace Q3.RouteB

/-! ## The two finite functionals of the shell -/

/-- `E² = ∑_{n=1}^{N} |Δ_n|²/n²`, the reciprocal-mode energy of the error row `Δ`
(the squared norm of `R Δ` with `R = diag(1/n)`; `|Δ_n|² = Δ_n²` for a real row). -/
def proposition59ReciprocalEnergySq (Δ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, Δ n ^ 2 / (n : ℝ) ^ 2

/-- `W = ∑_{n=1}^{N} |Δ_n|/n²`, the weighted error of an abstract real row `Δ`. -/
def proposition59ReciprocalWeightedError (Δ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, |Δ n| / (n : ℝ) ^ 2

/-- The abstract weighted error at `Δ = proposition59LatticeError v f L` is the
`W` of `proposition59_weighted_curvature_inequality`, on the nose. -/
theorem proposition59WeightedLatticeError_eq_reciprocal
    (v : ℤ → ℝ) (f : ℝ → ℝ) (L : ℝ) (N : ℕ) :
    proposition59WeightedLatticeError v f L N =
      proposition59ReciprocalWeightedError (proposition59LatticeError v f L) N := rfl

#print axioms proposition59WeightedLatticeError_eq_reciprocal

/-! ## Basel head and the two square-root constants -/

/-- `∑_{n=1}^{N} 1/n² ≤ π²/6` from `hasSum_zeta_two`. -/
private theorem head_zeta_two_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_two

/-- `√(π²/6) = π/√6`. -/
private theorem sqrt_zeta_two_const :
    Real.sqrt (Real.pi ^ 2 / 6) = Real.pi / Real.sqrt 6 := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_sq Real.pi_pos.le]

/-- `√(C/L⁴) = √C/L²` for `C ≥ 0` and `L > 0`. -/
private theorem sqrt_energy_const {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L) :
    Real.sqrt (C / L ^ 4) = Real.sqrt C / L ^ 2 := by
  rw [Real.sqrt_div hC, show L ^ 4 = (L ^ 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-! ## Item 1 — `NORMALITY_WEIGHT`: the energy controls the weighted error

`E² ≤ C/L⁴  ⟹  W ≤ (π/√6)·√C/L²`.  Cauchy–Schwarz on the split
`|Δ_n|/n² = (1/n)·(|Δ_n|/n)` with the Basel head `∑ 1/n² ≤ π²/6`. -/

/-- **Item 1** (`P59_RECIPROCAL_MODE_WEIGHTED_L2_SHELL`, NORMALITY_WEIGHT line). -/
theorem reciprocal_energy_to_weighted_error
    (Δ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hE : proposition59ReciprocalEnergySq Δ N ≤ C / L ^ 4) :
    proposition59ReciprocalWeightedError Δ N ≤
      Real.pi / Real.sqrt 6 * Real.sqrt C / L ^ 2 := by
  rw [proposition59ReciprocalWeightedError]
  have hE' : ∑ n ∈ Finset.Icc 1 N, Δ n ^ 2 / (n : ℝ) ^ 2 ≤ C / L ^ 4 := hE
  have hraw := Real.sum_mul_le_sqrt_mul_sqrt (Finset.Icc 1 N)
    (fun n : ℕ => (1 : ℝ) / (n : ℝ)) (fun n : ℕ => |Δ n| / (n : ℝ))
  simp only at hraw
  have hprod : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) * (|Δ n| / (n : ℝ)) =
      ∑ n ∈ Finset.Icc 1 N, |Δ n| / (n : ℝ) ^ 2 :=
    Finset.sum_congr rfl fun n _ => by ring
  have hA : ∑ n ∈ Finset.Icc 1 N, ((1 : ℝ) / (n : ℝ)) ^ 2 =
      ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 2 :=
    Finset.sum_congr rfl fun n _ => by ring
  have hB : ∑ n ∈ Finset.Icc 1 N, (|Δ n| / (n : ℝ)) ^ 2 =
      ∑ n ∈ Finset.Icc 1 N, Δ n ^ 2 / (n : ℝ) ^ 2 :=
    Finset.sum_congr rfl fun n _ => by rw [div_pow, sq_abs]
  rw [hprod, hA, hB] at hraw
  have ha : Real.sqrt (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 2) ≤
      Real.pi / Real.sqrt 6 := by
    rw [← sqrt_zeta_two_const]
    exact Real.sqrt_le_sqrt (head_zeta_two_le N)
  have hb : Real.sqrt (∑ n ∈ Finset.Icc 1 N, Δ n ^ 2 / (n : ℝ) ^ 2) ≤
      Real.sqrt C / L ^ 2 := by
    calc Real.sqrt (∑ n ∈ Finset.Icc 1 N, Δ n ^ 2 / (n : ℝ) ^ 2)
        ≤ Real.sqrt (C / L ^ 4) := Real.sqrt_le_sqrt hE'
      _ = Real.sqrt C / L ^ 2 := sqrt_energy_const hC hL
  calc ∑ n ∈ Finset.Icc 1 N, |Δ n| / (n : ℝ) ^ 2
      ≤ Real.sqrt (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 2) *
          Real.sqrt (∑ n ∈ Finset.Icc 1 N, Δ n ^ 2 / (n : ℝ) ^ 2) := hraw
    _ ≤ Real.pi / Real.sqrt 6 * (Real.sqrt C / L ^ 2) :=
        mul_le_mul ha hb (Real.sqrt_nonneg _) (by positivity)
    _ = Real.pi / Real.sqrt 6 * Real.sqrt C / L ^ 2 := by ring

#print axioms reciprocal_energy_to_weighted_error

/-! ## Item 2 — `IDENTIFICATION`: the energy controls every single node

`E² ≤ C/L⁴  ⟹  |Δ_n| ≤ n·√C/L²` for `1 ≤ n ≤ N`, hence at physical radius `X`
(indices `n ≤ X·L/(2π)`) the uniform bound `|Δ_n| ≤ X·√C/(2π·L)`.

The judge's `→ 0` is a statement about a *sequence* of cells; it is deliberately not
formalised here, because it needs the production coverage guard `N_k/L_k → ∞` and a
cofinal family.  The finite-cell inequality below is the whole content that a fixed
cell can carry. -/

/-- **Item 2** (`P59_RECIPROCAL_MODE_WEIGHTED_L2_SHELL`, IDENTIFICATION line),
per-node form: each coordinate satisfies `|Δ_n| ≤ n·E ≤ n·√C/L²`. -/
theorem reciprocal_energy_to_node_sup
    (Δ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hE : proposition59ReciprocalEnergySq Δ N ≤ C / L ^ 4)
    {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    |Δ n| ≤ (n : ℝ) * Real.sqrt C / L ^ 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hmem : n ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hn1, hnN⟩
  have hterm : Δ n ^ 2 / (n : ℝ) ^ 2 ≤ proposition59ReciprocalEnergySq Δ N :=
    Finset.single_le_sum (f := fun m : ℕ => Δ m ^ 2 / (m : ℝ) ^ 2)
      (fun i _ => by positivity) hmem
  have hsq : Real.sqrt (Δ n ^ 2 / (n : ℝ) ^ 2) ≤ Real.sqrt (C / L ^ 4) :=
    Real.sqrt_le_sqrt (hterm.trans hE)
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq hnpos.le,
    sqrt_energy_const hC hL] at hsq
  have hmul := mul_le_mul_of_nonneg_right hsq hnpos.le
  rw [div_mul_cancel₀ _ hnpos.ne'] at hmul
  calc |Δ n| ≤ Real.sqrt C / L ^ 2 * (n : ℝ) := hmul
    _ = (n : ℝ) * Real.sqrt C / L ^ 2 := by ring

#print axioms reciprocal_energy_to_node_sup

/-- **Item 2** at physical radius `X`: for `n ≤ X·L/(2π)` the node bound becomes
`|Δ_n| ≤ X·√C/(2π·L)`, uniform in `n`. -/
theorem reciprocal_energy_to_node_sup_at_radius
    (Δ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) {C L X : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hX : 0 < X)
    (hE : proposition59ReciprocalEnergySq Δ N ≤ C / L ^ 4)
    {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N)
    (hnX : (n : ℝ) ≤ X * L / (2 * Real.pi)) :
    |Δ n| ≤ X * Real.sqrt C / (2 * Real.pi * L) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hL2 : (0 : ℝ) < L ^ 2 := pow_pos hL 2
  have hpiL : (0 : ℝ) < 2 * Real.pi * L := mul_pos h2pi hL
  have hnode := reciprocal_energy_to_node_sup Δ hN hC hL hE hn1 hnN
  have hn2 : (n : ℝ) * (2 * Real.pi) ≤ X * L := by
    have hstep := mul_le_mul_of_nonneg_right hnX h2pi.le
    have hcancel : X * L / (2 * Real.pi) * (2 * Real.pi) = X * L := by
      field_simp
    linarith [hstep, hcancel.ge, hcancel.le]
  have hfac : (0 : ℝ) ≤ Real.sqrt C * L := mul_nonneg (Real.sqrt_nonneg C) hL.le
  refine hnode.trans ?_
  rw [div_le_div_iff₀ hL2 hpiL]
  calc (n : ℝ) * Real.sqrt C * (2 * Real.pi * L)
      = Real.sqrt C * L * ((n : ℝ) * (2 * Real.pi)) := by ring
    _ ≤ Real.sqrt C * L * (X * L) := mul_le_mul_of_nonneg_left hn2 hfac
    _ = X * Real.sqrt C * L ^ 2 := by ring

#print axioms reciprocal_energy_to_node_sup_at_radius

/-! ## Item 3 — H3, `P59_FULL_LATTICE_SUP_SHELL`

`sup_{1 ≤ n ≤ N} |Δ_n| ≤ C/L²  ⟹  W ≤ (π²/6)·C/L²`.  The `sup` hypothesis is written
as the pointwise family it is; no supremum object is introduced. -/

/-- **Item 3** (`P59_FULL_LATTICE_SUP_SHELL`). -/
theorem sup_error_to_weighted_error
    (Δ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hsup : ∀ n : ℕ, 1 ≤ n → n ≤ N → |Δ n| ≤ C / L ^ 2) :
    proposition59ReciprocalWeightedError Δ N ≤ Real.pi ^ 2 / 6 * (C / L ^ 2) := by
  have hCL : (0 : ℝ) ≤ C / L ^ 2 := div_nonneg hC (sq_nonneg L)
  calc proposition59ReciprocalWeightedError Δ N
      ≤ ∑ n ∈ Finset.Icc 1 N, C / L ^ 2 / (n : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' := Finset.mem_Icc.mp hn
        have hbound := hsup n hn'.1 hn'.2
        have hinv : (0 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hbound hinv
    _ = C / L ^ 2 * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ C / L ^ 2 * (Real.pi ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left (head_zeta_two_le N) hCL
    _ = Real.pi ^ 2 / 6 * (C / L ^ 2) := by ring

#print axioms sup_error_to_weighted_error

/-! ## Item 4 — composition with the alternating curvature inequality

`proposition59_weighted_curvature_inequality` (item 5 of verdict `f788d2fa`) reads

```
κ_F ≤ S_f + (L²/(2π²))·W + |T|
```

for a real symmetric row `v` with `v₀ ≠ 0` whose window transform has only real zeros.
Feeding item 1 into its `W` slot turns the energy hypothesis into a curvature bound
with **no** free error functional left. -/

/-- **Item 4**: the reciprocal-mode energy hypothesis bounds the alternating lattice
curvature, `κ_F ≤ S_f + (L²/(2π²))·(π/√6)·√C/L² + |T|`. -/
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
        |proposition59ScaledAlternatingTail L N| := by
  have hmain := proposition59_weighted_curvature_inequality hL N v hv hv0 hzeros f
  rw [proposition59WeightedLatticeError_eq_reciprocal] at hmain
  have hW := reciprocal_energy_to_weighted_error (proposition59LatticeError v f L)
    hN hC hL hE
  have hc : (0 : ℝ) ≤ L ^ 2 / (2 * Real.pi ^ 2) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hW hc
  linarith [hmain, hscaled]

#print axioms reciprocal_energy_to_curvature_bound

/-! ## What is open

The shell's single open input is unchanged and unproved:

```
P59_RECIPROCAL_MODE_XI_LATTICE_ERROR_ENERGY_BOUND
  ∃ C ≥ 0, ∀^∞ k,  ∑_{n=1}^{N_k} |(-1)^n ξ_{k,n}/ξ_{k,0} − centeredXi(x_{k,n})/centeredXi(0)|² / n²
                   ≤ C / L_k⁴
```

Nothing in this file supplies it, and nothing here is a statement about `centeredXi`:
`Δ` is an arbitrary real sequence and the energy bound is a hypothesis in every
theorem.  Likewise the verdict's `COVERAGE_GUARD` (`N_k/L_k → ∞`) and the `→ 0` of the
IDENTIFICATION line are cofinal statements about a family of cells; they are not
derived from the finite inequalities above and are not claimed.

`sup_error_to_weighted_error` is the H3 implication only; the sup-rate
`sup_n |Δ_n| ≤ C/L²` is H3's own open input.
-/

end Q3.RouteB
