PACKET 3 FOR MYTHOS — routing-table items (1), (2) + transcribed Goal 043
Repo: Malaeu/chen_q3 · branch rh_clean · HEAD f60f08e14134ac244e14b9c3ae68db3e8b45b646
Built: 2026-07-31 by conductor-CLI (Linux). Encoding: UTF-8, LF.

COVER NOTE:
1. Item (1): muntz_r6 TailAnalyticity.lean IN FULL — Rminus_differentiableOn_halfPlane
   and its Estar lemmas.
2. Item (2), label EXCERPT-main-lean-lines-1-60: frozen Main.lean lines 1-60 verbatim
   (defs Estar/Gwin/Rminus/Rplus/H) for your promotion card. Consumer hypothesis type
   sits at line 157: hRm : AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane.
3. Goal 043 transcribed, on the bus (SHA-256 prefix 5531ef30, HEAD above), source-
   locked both sides. Conductor PHASE-0 pre-scan flags three candidate gaps for the
   inventory (orientation only, NOT prejudged): DifferentiableOn vs AnalyticOnNhd
   passage; R6 GLOBAL LipschitzWith vs v3 hypothesis class; possible Rminus/Estar
   definitional divergence between the two RequestProjects.
4. Item (3) Thm 5.10 (arXiv 2511.22755): owner acquisition, pending, later packet.
5. Item (4) 043.answer: after Codex execution.

VERIFICATION CONTRACT: payloads strictly between BEGIN/END markers (markers excluded,
exactly one trailing newline included). Recompute SHA-256 over exactly those bytes.

MANIFEST (label · bytes · sha256):
  docs/routeB_bus/muntz_r6/RequestProject/TailAnalyticity.lean · 6241 · 88ba75b8b28df9a6b826f339a002c6e9af6c2263ccc4f79f022b0c2b99b87fc5
  EXCERPT-main-lean-lines-1-60 · 2178 · d334048e38ea4d443d9bc6d978c86d45d1dfb8d9bad09db58443c5db66d51710
  docs/routeB_bus/043_muntz_v3_supplier_hrm.goal.md · 4416 · 5531ef30cf15d1372bb3174a421695c8816d7719b0bf1eef06a0afe762c5e786

═══ FILE BEGIN: docs/routeB_bus/muntz_r6/RequestProject/TailAnalyticity.lean ═══
import RequestProject.WindowAnalyticity

open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology BigOperators

namespace EStarMuntzZeroMassContinuation

/-- The concrete right tail is entire. -/
theorem Rplus_differentiable
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Differentiable ℂ (Rplus h Λ) := by
  -- Since h is supported in [a, b], Estar h u = 0 for u > b
  -- So Rplus h Λ is an integral over a bounded interval, hence entire
  intro s
  -- Rewrite Rplus as integral over (Λ, b] ∩ (Λ, ∞)
  have hsupp' : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0 := by
    intro v hv
    apply hsupp
    intro hvab
    apply hv
    exact ⟨ha.le.trans hvab.1, hvab.2⟩
  -- For u > b, Estar h u = 0
  have hEstar_zero : ∀ u, b < u → Estar h u = 0 := fun u hu =>
    Estar_eq_zero_of_gt h b u (by linarith) hsupp' hu
  -- Define f as indicator of Estar h on (Λ, b]
  let f : ℝ → ℂ := Set.Ioc Λ b |>.indicator (Estar h)
  have hfmeas : Measurable f :=
    (Estar_measurable h a b ha hsupp hlip.continuous.measurable).indicator measurableSet_Ioc
  -- f is locally integrable on (0, ∞)
  have hlocal0 := Estar_locallyIntegrableOn_Ioi h a b ha hab K hsupp hlip
  have hlocal : LocallyIntegrableOn f (Set.Ioi 0) := by
    apply hlocal0.mono hfmeas.aestronglyMeasurable
    filter_upwards with u
    simp [f, Set.indicator_apply]
    split_ifs <;> simp
  -- f =O[atTop] x^(-A) for any A (since f = 0 for x > b)
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have htop : ∀ A : ℝ, f =O[atTop] (fun x : ℝ => x ^ (-A)) := by
    intro A
    apply (isBigO_zero (fun x : ℝ => x ^ (-A)) atTop).congr'
    · filter_upwards [eventually_gt_atTop b] with x hx
      symm
      simp [f, not_and_of_not_right _ (by linarith : ¬ x ≤ b)]
    · rfl
  -- f =O[𝓝[>] 0] x^(-B) for any B (since f = 0 near 0 for x ≤ Λ)
  have hbot : ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-B)) := by
    intro B
    apply (isBigO_zero (fun x : ℝ => x ^ (-B)) (𝓝[>] (0 : ℝ))).congr'
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hΛpos)] with x hx
      symm
      simp [f, (by linarith : ¬ Λ < x)]
    · rfl
  -- Rplus h Λ = mellin f
  have heq : Rplus h Λ = mellin f := by
    funext s
    unfold Rplus mellin
    simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with u
    simp only [f, Set.indicator_apply]
    by_cases huLambda : Λ < u
    · by_cases hu0 : 0 < u
      · by_cases huIoc : u ∈ Set.Ioc Λ b
        · -- Λ < u, 0 < u, u ∈ Ioc Λ b
          simp [huLambda, hu0, huIoc, smul_eq_mul, mul_comm]
        · -- Λ < u, 0 < u, u ∉ Ioc Λ b
          -- u > Λ and u ∉ (Λ, b] means u > b, so Estar h u = 0
          have hu_gt_b : b < u := by
            simp only [Set.mem_Ioc] at huIoc
            push_neg at huIoc
            tauto
          rw [hEstar_zero u hu_gt_b]
          simp
      · -- Λ < u, ¬(0 < u) → contradiction since Λ ≥ 1
        linarith
    · -- ¬(Λ < u), so LHS = 0
      simp [huLambda]
  rw [heq]
  exact mellin_differentiableAt_of_isBigO_rpow hlocal (htop (s.re + 1)) (by linarith)
    (hbot (s.re - 1)) (by linarith)

/-- The zero-mass left tail is holomorphic on `re s > -1/2`. -/
theorem Rminus_differentiableOn_halfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    DifferentiableOn ℂ (Rminus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re} := by
  obtain ⟨C, hC⟩ :=
    Estar_bounded_by_sqrt_of_zeroMass h a b ha hab K hsupp hlip hmass
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let f : ℝ → ℂ := Set.Ioo (0 : ℝ) (Λ⁻¹) |>.indicator (Estar h)
  have hfmeas : Measurable f :=
    (Estar_measurable h a b ha hsupp hlip.continuous.measurable).indicator measurableSet_Ioo
  have hlocal0 := Estar_locallyIntegrableOn_Ioi h a b ha hab K hsupp hlip
  have hlocal : LocallyIntegrableOn f (Set.Ioi 0) := by
    apply hlocal0.mono hfmeas.aestronglyMeasurable
    filter_upwards with u
    simp only [f, Set.indicator_apply]
    split_ifs <;> simp
  have htop : ∀ A : ℝ, f =O[atTop] (fun x : ℝ => x ^ (-A)) := by
    intro A
    apply (isBigO_zero (fun x : ℝ => x ^ (-A)) atTop).congr'
    · filter_upwards [eventually_gt_atTop (Λ⁻¹)] with x hx
      symm
      simp [f, (by linarith : ¬ x < Λ⁻¹)]
    · rfl
  have hbot : f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(-(1 : ℝ) / 2))) := by
    rw [isBigO_iff]
    refine ⟨max C 0, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (show 0 < (1 : ℝ) by norm_num))]
      with u hu hu1
    have hu0 : 0 < u := hu
    have hsqrt := hC u ⟨hu0, hu1⟩
    simp only [f, Set.indicator_apply]
    by_cases hui : u ∈ Set.Ioo (0 : ℝ) (Λ⁻¹)
    · rw [if_pos hui]
      rw [Real.sqrt_eq_rpow] at hsqrt
      have hexp : (1 / 2 : ℝ) = -(-(1 : ℝ) / 2) := by norm_num
      rw [hexp] at hsqrt
      have hrpow_nonneg : 0 ≤ u ^ (-(-(1 : ℝ) / 2)) := Real.rpow_nonneg hu0.le _
      rw [Real.norm_eq_abs, abs_of_nonneg hrpow_nonneg]
      exact hsqrt.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) hrpow_nonneg)
    · rw [if_neg hui, norm_zero]
      positivity
  have heq : Rminus h Λ = mellin f := by
    funext s
    unfold Rminus mellin
    rw [← MeasureTheory.integral_indicator measurableSet_Ioo]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with u
    simp only [f, Set.indicator_apply]
    by_cases hu : u ∈ Set.Ioo (0 : ℝ) (Λ⁻¹)
    · simp [hu, hu.1, smul_eq_mul, mul_comm]
    · by_cases hu0 : 0 < u
      · simp [hu, hu0]
      · simp [hu, hu0]
  intro s hs
  rw [heq]
  exact (mellin_differentiableAt_of_isBigO_rpow hlocal (htop (s.re + 1)) (by linarith)
    hbot hs).differentiableWithinAt

end EStarMuntzZeroMassContinuation
═══ FILE END: docs/routeB_bus/muntz_r6/RequestProject/TailAnalyticity.lean ═══

═══ FILE BEGIN: EXCERPT-main-lean-lines-1-60 ═══
import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Set Filter MeasureTheory Complex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace EStarMuntzZeroMassContinuation

noncomputable def Estar (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  Real.sqrt u * ∑' n : ℕ+, h (n * u)

noncomputable def Mellin (k : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), k u * (u : ℂ) ^ (s - 1)

noncomputable def Gwin (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioo (Λ⁻¹) Λ, Estar h u * (u : ℂ) ^ (s - 1)

noncomputable def Rminus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioo (0 : ℝ) (Λ⁻¹), Estar h u * (u : ℂ) ^ (s - 1)

noncomputable def Rplus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi Λ, Estar h u * (u : ℂ) ^ (s - 1)

def H : Set ℂ := {w : ℂ | 0 < w.re}

noncomputable def MellinDivOne (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  dslope (Mellin h) 1 w

noncomputable def ZetaResidueFactor : ℂ → ℂ :=
  Function.update (fun z => (z - 1) * riemannZeta z) 1 1

noncomputable def ZetaMellinPoleSub (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  ZetaResidueFactor w * MellinDivOne h w

lemma one_mem_H : (1 : ℂ) ∈ H := by simp [H]

/-- At `s = 1`, the Mellin kernel is one, so zero mass gives a zero. -/
theorem mellin_one_eq_zero (h : ℝ → ℂ)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0) : Mellin h 1 = 0 := by
  simpa [Mellin] using hmass

lemma mellinDivOne_value_one (h : ℝ → ℂ) :
    MellinDivOne h 1 = deriv (Mellin h) 1 := by
  simp [MellinDivOne, dslope_same]

lemma mellinDivOne_of_ne (h : ℝ → ℂ) {w : ℂ} (hw : w ≠ 1) :
    MellinDivOne h w = (Mellin h w - Mellin h 1) / (w - 1) := by
  rw [MellinDivOne, dslope_of_ne (Mellin h) hw]
  simp [slope, div_eq_inv_mul, mul_comm]

lemma mellinDivOne_of_ne_of_zero (h : ℝ → ℂ) (hz : Mellin h 1 = 0)
    {w : ℂ} (hw : w ≠ 1) : MellinDivOne h w = Mellin h w / (w - 1) := by
  rw [mellinDivOne_of_ne h hw, hz, sub_zero]
═══ FILE END: EXCERPT-main-lean-lines-1-60 ═══

═══ FILE BEGIN: docs/routeB_bus/043_muntz_v3_supplier_hrm.goal.md ═══
# Goal 043 — MuntzV3 Supplier hRm: Rminus analyticity on shiftedHalfPlane

ISSUED: 2026-07-31, Mythos (dispatch answer to packet 2; transcribed by conductor-CLI
  on owner's order, source-lock verified against Main.lean and muntz_r6)
MODE: LOCAL_FIRST · NO_ARISTOTLE_SUBMISSION_IN_THIS_CYCLE
SCOPE: ABSTRACT · VERIFIER TARGET: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen files untouched
ORIGIN: Mythos K2 ranking — of the four retained inputs (hG/hRm/hRp/habs), hRm is the
  only one whose proof already exists in the repo (RULE_INVENTORY_FIRST applied to
  dispatch itself). Parallel non-Lean track (Mythos cycle, not this goal): promotion
  card — which mainline node an unconditional T5 would close.

## Consumer (exact T5 input type, source-locked)

docs/routeB_bus/muntz_v3/RequestProject/Main.lean:157
(continued_window_identity_of_analytic hypothesis):

```lean
hRm : AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane
```

Target theorem (new file, name binding):

```lean
theorem rminus_analyticOnNhd_shiftedHalfPlane
    (h : ℝ → ℂ) (Λ : ℝ) (…hypotheses per PHASE 0 inventory…) :
    AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane
```

Hypothesis set is NOT prescribed here: it is the OUTPUT of PHASE 0 (whatever the R6
supplier needs, translated to the v3 objects; no silent strengthening beyond what R6
actually uses; every hypothesis named in the answer).

## Supplier candidate (inventory anchor)

docs/routeB_bus/muntz_r6/RequestProject/TailAnalyticity.lean:

```lean
theorem Rminus_differentiableOn_halfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    DifferentiableOn ℂ (Rminus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re}
```

## PHASE 0 (mandatory, before any promise)

Inventory diff between supplier and consumer. Answer MUST resolve, each with a
one-line verdict:

1. Same `Rminus` object? (v3 Main.lean def vs muntz_r6 def — byte-compare the
   definitions and their `Estar` dependencies.)
2. Same half-plane? (`shiftedHalfPlane` vs `{s : ℂ | -(1:ℝ)/2 < s.re}` — definitional
   or bridge needed.)
3. `DifferentiableOn` → `AnalyticOnNhd` passage (openness of the half-plane +
   Mathlib `DifferentiableOn.analyticOnNhd`-class API — name the exact lemma).
4. Hypothesis set on h / Estar / Λ: R6 uses GLOBAL `LipschitzWith` — record whether
   the consumer context can supply it or a bridge from the v3 hypothesis class is
   required (report, do not silently strengthen).

PHASE 0 output is exactly one of:

```text
CONSUMPTION_WRAPPER          (all four resolve; proceed to PHASE 1)
DOMAIN_BRIDGE_NEEDED         (name the exact bridge lemma to prove)
R6_OBJECT_MISMATCH           (exact diff of the two Rminus/Estar definitions)
```

## PHASE 1

Wrapper (or the minimal named bridge) in a NEW file inside muntz_v3/RequestProject/.
Reuse R6 — do NOT reprove its content.

## Forbidden

- modifying frozen files (Main.lean, MellinCompactSupportAnalyticity.lean);
- reproving R6 content;
- numerical integration;
- taint (sorry | admit | axiom | native_decide | exact?);
- three-input bundle (hG/hRp/habs are SEPARATE future contracts);
- any Route B / RH status promotion.

## Validation

```text
lake env lean <touched-file>
lake build
grep taint terms
#print axioms rminus_analyticOnNhd_shiftedHalfPlane
axioms must be exactly [propext, Classical.choice, Quot.sound]
```

## Success code

HRM_SUPPLIER_DISCHARGED

## Failure codes (exactly one, fail-closed)

R6_DOMAIN_MISMATCH
R6_HYPOTHESIS_GAP(named)
ESTAR_BOUND_GAP(named edge)
LEAN_BUILD_FAIL

## Registered predictions (before execution)

P043-M1 (Mythos): wrapper ≤ 80 lines, no new analysis.
P043-M2 (Mythos): friction = domain shift / Λ-parameter bookkeeping only.
P043-M3 (Mythos): on mismatch the gap names itself in one line (a concrete Estar
  bound at one edge).

## Answer requirements

043_muntz_v3_supplier_hrm.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS LOG (else
REJECTED); scope/verifier tags on every claim; PHASE 0 verdicts explicit; scoring of
P043-M1..M3; goal consumed by SHA-256 stated; one non-promoting Route B state-history
row; ROUTE_B_STATE update last; canon + mirror in one transaction; report — do not
repair — any divergence.
═══ FILE END: docs/routeB_bus/043_muntz_v3_supplier_hrm.goal.md ═══

