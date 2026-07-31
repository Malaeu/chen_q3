PACKET 3b FOR MYTHOS — FULL routing-table delivery (supersedes packet 3, which was
never pasted). Repo: Malaeu/chen_q3 · rh_clean · HEAD 5f5b482987cdb4cebd0df5aea5607af9c2a12a0a
Built: 2026-07-31 by conductor-CLI (Linux). UTF-8, LF.

COVER NOTE — items keyed to YOUR updated list:
(1) PARENT file of the Müntz lemma = 012 answer: the local run that proved the
    windowed Mellin identity in the absolute region and RETURNED the named missing
    lemma EStarMuntzZeroMassContinuation (line 7). Plus ORDER = the archived v1
    standalone task carrying the exact commissioning text ("integration happens
    elsewhere"). These two are your source-locked kill-test material for the
    Müntz -> S2 edge.
(2) R6 TailAnalyticity.lean in full (Rminus_differentiableOn_halfPlane + Estar lemmas).
(3) EXCERPT-main-lean-lines-1-60: frozen Main.lean defs verbatim (Estar/Gwin/Rminus/
    Rplus/H). Consumer type at line 157: hRm : AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane.
(4) THM510 acquisition COMPLETE (owner task closed same day): Connes-Consani-Moscovici,
    "Zeta Spectral Triples", arXiv 2511.22755. Verbatim theorem (real zeros = spectrum
    of selfadjoint D_log), their Outlook two-limit strategy, their §8 missing steps
    (smallest eigenvalue SIMPLE + eigenvector EVEN; k_λ ≈ ξ_λ control), cross-links
    to our prolate layer. Full PDF is on the bus: docs/routeB_bus/imports/2511.22755.pdf.
(5) ROUTE_B_THEOREM_CONTRACT v2 — for substantive H1/H3 coloring on the next canvas.

STATUS: Goal 043 in execution (Codex PHASE 0 running; R6 TailAnalyticity already
builds inside the v3 project, 8032 jobs — cross-project import viable). 043.answer
arrives in packet 4.

QUESTIONS (dispatch, in order of kill-power):
(a) Kill-test the Müntz -> S2 edge on items (1): SIGN it, KILL it, or name the one
    missing fact that decides.
(b) Confirm/correct the H2b entry against item (4); if the extraction misses what the
    promotion card needs, name exact pages for the next packet.
(c) Color H1/H3 substantively from item (5) on canvas v2.
(d) Promotion card: fill format + verdict after (a).

VERIFICATION CONTRACT: payloads strictly between BEGIN/END markers (markers excluded,
exactly one trailing newline included). Recompute SHA-256 over exactly those bytes.

MANIFEST (label · bytes · sha256):
  PARENT: docs/routeB_bus/012_estar_windowed_mellin_crosswalk.answer.md · 4694 · e28ff3028aa04966b2718cf9fcba3f0f5923afe00a18b3e02491953e862a37a5
  ORDER: archive ARISTOTLE_TASK_EStarMuntzContinuation_v1.md · 4826 · 99fba49692fb9eec900e45a5f864572b77d7ea974739d1b7beed0f12c57f81d6
  R6: docs/routeB_bus/muntz_r6/RequestProject/TailAnalyticity.lean · 6241 · 88ba75b8b28df9a6b826f339a002c6e9af6c2263ccc4f79f022b0c2b99b87fc5
  EXCERPT-main-lean-lines-1-60 · 2178 · d334048e38ea4d443d9bc6d978c86d45d1dfb8d9bad09db58443c5db66d51710
  THM510: docs/routeB_bus/imports/THM510_ZETA_SPECTRAL_TRIPLES_2026-07-31.md · 3284 · 68552e06303140284147e6e0e1d5e2539951f695d5ec0e1ac45b00ca2c67313f
  CONTRACT: q3.lean.aristotle/docs/ROUTE_B_THEOREM_CONTRACT_v2.md · 12099 · 7e1d2309d9d157e573319ea4aef4238f276a061efd6f437f235009077abc0171
  GOAL043: docs/routeB_bus/043_muntz_v3_supplier_hrm.goal.md · 4416 · 5531ef30cf15d1372bb3174a421695c8816d7719b0bf1eef06a0afe762c5e786

═══ FILE BEGIN: PARENT: docs/routeB_bus/012_estar_windowed_mellin_crosswalk.answer.md ═══
# 012 — EStarWindowedMellinCrosswalk

Date: `2026-07-27`

```text
ESTAR_CONTINUATION_LEMMA_MISSING
missing lemma: EStarMuntzZeroMassContinuation
```

## Lean artifact

```text
Q3/Proofs/RouteB/EStarWindowedMellinCrosswalk.lean
720 lines
```

The source function remains parametric:

```lean
h : ℝ → ℂ
hmass : ZeroPositiveMass h
```

No concrete `hTrial_m` is selected in the file.

## T1 — exact finite-window identity

Main declarations:

```lean
WindowFiniteSupport
dirichletWindow
dirichletWindow_eq_constraint_sum
windowedMellin_E_star_eq_weightedDirichletWindowIntegral
```

The proved kernel is

\[
D_{\lambda,p}(v)
=\sum_{n\in S}
  \mathbf 1_{\{v/\lambda\le n\le v\lambda\}}\,n^{-p}.
\]

The proved identity is

\[
\mathcal M\!\left(
  1_{[\lambda^{-1},\lambda]}\mathcal E_*h
\right)(s)
=
\int_0^\infty
  v^{s-\frac12}h(v)D_{\lambda,s+\frac12}(v)\,dv.
\]

The only comb used under the integral is the finite `Finset S`.  The bridge
back to the D0 `E_star` is the explicit `WindowFiniteSupport` certificate.
There is no infinite sum/integral exchange in T1.

## T2 — zero-mass decomposition in the absolute domain

Main declarations:

```lean
ZeroPositiveMass
EStarMellinAbsolute
lowerMellinTail
upperMellinTail
mellin_E_star_eq_riemannZeta_mul
windowedMellin_E_star_zeroMass_decomposition_abs
```

Under

```lean
hmass : ZeroPositiveMass h
hp    : 1 < (s + 1 / 2).re
habs  : EStarMellinAbsolute h (s + 1 / 2)
hEconv : MellinConvergent (E_star h) s
1 ≤ lambda
```

Lean proves

\[
\mathcal M\!\left(
  1_{[\lambda^{-1},\lambda]}\mathcal E_*h
\right)(s)
=
\zeta\!\left(s+\tfrac12\right)
  \mathcal M(h)\!\left(s+\tfrac12\right)
-R^-_\lambda(s)-R^+_\lambda(s),
\]

with exact definitions

\[
R^-_\lambda(s)=
\mathcal M(1_{(-\infty,\lambda^{-1})}\mathcal E_*h)(s),
\qquad
R^+_\lambda(s)=
\mathcal M(1_{(\lambda,\infty)}\mathcal E_*h)(s).
\]

No bound or smallness claim is made for either tail.

### Post-audit scope note

In the absolute-domain theorem, `hmass` is deliberately present but
definitionally unused: the proof locks and clears it.  Zero mass is required
for the continuation into the strip, not for the absolute-domain algebra.
Thus `zeroMass_decomposition_abs` is a stronger name than the minimal
absolute-domain contract.

The local Q3 semantic search and the Mathlib source scan found the scaling,
Mellin-holomorphy, and zeta Dirichlet-series ingredients, but no theorem that
continues this zero-mass identity from the absolute domain to
`|Re s| < 1/2`.  That continuation is isolated as the missing lemma named in
the status block; it is not represented by an axiom or a hole.

## Mandatory nonzero-mass pole plant

```lean
nonzeroMassPlant v = 1_(0,1](v)
```

Lean proves:

```text
nonzeroMassPlant ≥ 0
integral_(0,∞) nonzeroMassPlant = 1
not ZeroPositiveMass(nonzeroMassPlant)
```

For

\[
J_\lambda(t)=
\frac{\lambda^{1/2-t}-\lambda^{t-1/2}}{1/2-t},
\]

Lean proves the exact pole-window ratio

\[
\frac{J_\lambda(-\sigma)}{J_\lambda(0)}
=
\frac{\lambda^\sigma}{1+2\sigma}
\cdot
\frac{1-\lambda^{-1-2\sigma}}{1-\lambda^{-1}}
\ge
\frac{\lambda^\sigma}{1+2\sigma}
\qquad(\lambda>1,\ \sigma\ge0).
\]

Thus the mass-one plant retains the registered `lambda^sigma` pole growth.
A bounded implementation would not satisfy these proved identities.

This indicator is a pole-counterterm plant, not a plant in the T2 Lipschitz
regularity class.  The triangular Lipschitz PL2 is not discharged by 012 and
remains an explicit obligation of the repaired v2 continuation contract.

The standalone continuation contract v1 is separately archived
`FATAL / DO_NOT_EXECUTE` under `ZETA_RAW_POLE_VALUE_MISMATCH`; this does not
invalidate the absolute-domain identities proved in 012.

## Validation

```text
lake env lean Q3/Proofs/RouteB/EStarWindowedMellinCrosswalk.lean
exit: 0

lake build
exit: 0
Build completed successfully (7817 jobs).

#print axioms declarations checked: 29
each result: [propext, Classical.choice, Quot.sound]
sorryAx: 0

grep sorry/admit/exact?/native_decide/@[implemented_by]/axiom
matches in new Lean file: 0
```

## Source locks

```text
9b8bb057708b1d04a21c27c1aebaf10fdeb6d7fd5851ee5f3638d33ce2f63e05
  Q3/Proofs/RouteB/EStarWindowedMellinCrosswalk.lean

a322424d51aad88d4ee2d366220ad6ea2c4cea02c96bc07a6d97f247203b7a97
  012_estar_windowed_mellin_crosswalk.goal.md

ed2217c1b65cf640b388fc26586f9eeb56340fcee8b7e06402c88f053381b3fa
  proshka/PROSHKA_MELLIN_CROSSWALK_2026-07-27.md

aabaf47cb484f0157fd7b2ac4f30811aec9595116c1193715e41de8b520393cd
  Q3/Proofs/RouteB/D0KTrialStage2.lean
```

## State

```text
ROUTE_B_STATE.md: untouched
ROUTE_B_EXECUTION_STATE.json: untouched
Bus 010: not created
Project status: CHALLENGER / NOT_RH
```
═══ FILE END: PARENT: docs/routeB_bus/012_estar_windowed_mellin_crosswalk.answer.md ═══

═══ FILE BEGIN: ORDER: archive ARISTOTLE_TASK_EStarMuntzContinuation_v1.md ═══
TASK:
EStarMuntzZeroMassContinuation_Standalone

CONTEXT (one line):
Self-contained task: Mathlib only, no project files. A local run proved the
windowed Mellin identity for a dilation-sum operator in the absolute region
and returned the named missing lemma: analytic continuation of the identity
into the critical strip under a zero-mass hypothesis. Supply that lemma as a
reusable standalone file (integration happens elsewhere, offline).

SETUP (define inside the file; everything parametric):
  variables (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
  (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
  (hlip : LipschitzWith K h)                      -- or ContDiff ℝ 1 h; choose
  (hmass : ∫ v in Set.Ioi (0:ℝ), h v = 0)
  (Λ : ℝ) (hΛ : 1 ≤ Λ)

  noncomputable def Estar (h : ℝ → ℂ) (u : ℝ) : ℂ :=
    Real.sqrt u * ∑' n : ℕ+, h (n * u)
  -- for u > 0 the sum has finitely many nonzero terms (support in [a,b]).

  noncomputable def Mellin (k : ℝ → ℂ) (s : ℂ) : ℂ :=
    ∫ u in Set.Ioi (0:ℝ), k u * (u : ℂ) ^ (s - 1)

  noncomputable def Gwin (s : ℂ) : ℂ :=
    ∫ u in Set.Ioo (Λ⁻¹) Λ, Estar h u * (u : ℂ) ^ (s - 1)

  noncomputable def Rminus (s : ℂ) : ℂ :=
    ∫ u in Set.Ioo (0:ℝ) (Λ⁻¹), Estar h u * (u : ℂ) ^ (s - 1)
  noncomputable def Rplus (s : ℂ) : ℂ :=
    ∫ u in Set.Ioi Λ, Estar h u * (u : ℂ) ^ (s - 1)

TARGET DECLARATIONS (all with no sorry):

T1 (trivial tail): ∀ u > b, Estar h u = 0; hence Rplus is an integral over
   the compact interval [Λ, max b Λ] and s ↦ Rplus s is entire.

T2 (analytic heart — bounded Riemann sums from zero mass):
   ∃ C, ∀ u ∈ Set.Ioo (0:ℝ) 1, ‖∑' n : ℕ+, h (n * u)‖ ≤ C.
   Route: the sum times u is a Riemann sum of ∫ h over mesh u; compare with
   the integral via the Lipschitz bound on each cell intersecting [a,b]
   (at most (b − a)/u + 2 cells, each error ≤ K·u·u ⇒ total error
   ≤ K·u·(b − a + 2u)); the integral itself is 0 by hmass; divide by u.
   Corollary: ∃ C', ∀ u ∈ Set.Ioo (0:ℝ) 1, ‖Estar h u‖ ≤ C' * Real.sqrt u.

T3 (left tail analytic): s ↦ Rminus s is differentiable (analytic) on
   {s : ℂ | -1/2 < s.re}. (Integrand dominated by C'·u^{Re s − 1/2} near 0.)

T4 (zeta side analytic under zero mass):
   Mellin h is entire (compact support away from 0), Mellin h 1 = 0 (= hmass),
   and s ↦ riemannZeta (s + 1/2) * Mellin h (s + 1/2) is differentiable on
   {s : ℂ | -1/2 < s.re}: the only candidate singularity s = 1/2 is removable
   because the simple pole of ζ at 1 has residue multiplied by Mellin h 1 = 0.
   (Route: write ζ(w) = 1/(w−1) + entire-part via Mathlib's
   riemannZeta_sub_one_div... / completedRiemannZeta API, or use
   Complex.analyticAt of (w−1)·ζ(w) together with the factor vanishing.)

T5 (MAIN — continuation): given the absolute-region identity as a hypothesis
   (habs : ∀ s : ℂ, 1/2 < s.re →
      Gwin s = riemannZeta (s + 1/2) * Mellin h (s + 1/2) - Rminus s - Rplus s),
   conclude
      ∀ s : ℂ, -1/2 < s.re →
      Gwin s = riemannZeta (s + 1/2) * Mellin h (s + 1/2) - Rminus s - Rplus s.
   Route: Gwin is entire (integral of an entire-in-s integrand over a compact
   window with integrable bound); T1+T3+T4 make the right side analytic on the
   connected open set {Re s > −1/2}; both sides agree on the nonempty open
   subset {Re s > 1/2}; apply the identity theorem for analytic functions
   (AnalyticOn.eqOn_of_preconnected_of_eventuallyEq or the Mathlib equivalent).

PL (plant — zero mass is load-bearing): for an explicit Lipschitz bump
   h₀ ≥ 0 supported in [1,2] with ∫ h₀ ≠ 0, show the conclusion of T2 FAILS:
   the sums ∑ h₀(n u) grow like (∫h₀)/u as u → 0 (exhibit a quantitative
   lower bound along u = 1/k), so Estar h₀ u ≳ u^{-1/2}. No smallness talk;
   a lower bound along a sequence suffices.

FORBIDDEN:
- no new axioms, no native_decide, no sorry/admit;
- fully self-contained: import Mathlib only; do not reference any external
  project names;
- do not change the Mellin convention above;
- no claims about ζ zeros, RH, or anything beyond the stated targets.

VALIDATION:
- lake build succeeds; #print axioms for T1–T5 and PL:
  exactly [propext, Classical.choice, Quot.sound];
- grep sorry/admit/axiom/native_decide: clean;
- report which Mathlib lemmas supplied (i) the ζ pole/entire-part API,
  (ii) the identity theorem, (iii) differentiability under the integral sign
  (or the workaround used).

RETURN EXACTLY ONE PRIMARY STATUS:
ESTAR_MUNTZ_CONTINUATION_PROVED
RIEMANN_SUM_LIPSCHITZ_GAP
  (if the T2 cell-counting bound cannot be assembled — name the exact
   missing Mathlib piece)
ZETA_POLE_API_GAP
  (if the removable-singularity step at s = 1/2 lacks API — name it)
═══ FILE END: ORDER: archive ARISTOTLE_TASK_EStarMuntzContinuation_v1.md ═══

═══ FILE BEGIN: R6: docs/routeB_bus/muntz_r6/RequestProject/TailAnalyticity.lean ═══
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
═══ FILE END: R6: docs/routeB_bus/muntz_r6/RequestProject/TailAnalyticity.lean ═══

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

═══ FILE BEGIN: THM510: docs/routeB_bus/imports/THM510_ZETA_SPECTRAL_TRIPLES_2026-07-31.md ═══
# IMPORT ACQUISITION — Theorem 5.10, "Zeta Spectral Triples"

Acquired: 2026-07-31 by conductor-CLI (owner task from Mythos routing table, item 3).
Source: arXiv 2511.22755 — Alain Connes, Caterina Consani, Henri Moscovici,
*Zeta Spectral Triples*. PDF stored alongside: `imports/2511.22755.pdf` (668 KB).
Extraction: pdftotext; formulas may carry OCR artifacts — the PDF is authoritative.
K7 classification: Theorem 5.10 itself = THEOREM (proved in the paper).
The RH strategy built on it = CONDITIONAL (the paper's own §8 "The missing steps").

## Theorem 5.10 (verbatim modulo OCR)

Let ε_N be the smallest eigenvalue of QW_λ^N assumed simple and ξ the corresponding
eigenvector assumed even, normalized by δ_N(ξ) = 1.

(i) The operator D_log^(λ,N) is selfadjoint in the direct sum E_N ⊕ E_N^⊥ where on
    the subspace E'_N = E_N / Cξ the inner product is given by the restriction of
    the quadratic form QW_λ − ε_N⟨|⟩.

(ii) The regularized determinant of D_log^(λ,N) is given by

    det_reg(D_log^(λ,N) − z) = −i λ^{−iz} ξ̂(z)

    where ξ̂ is the Fourier transform of ξ for the duality ⟨R*₊ | R⟩.

(iii) The Fourier transform ξ̂(z) is an entire function, ALL ITS ZEROS ARE ON THE
    REAL LINE and coincide with the spectrum of D_log^(λ,N).

## Why this is the mainline entry (map: импорт Thm 5.10 → S2 cluster · H2b)

Clause (iii) is an H2-machine: an explicit finite-dimensional construction whose
associated entire function has provably REAL zeros (selfadjoint spectrum ⇒ real).
The paper's Outlook then states the two-limit strategy:

- fixed λ, N → ∞: det_reg(D_log^(λ,N) − s) → −i λ^{−iz} ξ̂_λ(z);
- λ → ∞: ξ̂_λ (suitably normalized) → Riemann's Ξ uniformly on closed substrips of
  |Im z| < 1/2; convergence would entail RH via Hurwitz.

This is structurally OUR H1–H4 ladder (entire approximants, real zeros, strip
tracking, decay) built from the Weil quadratic form + prolate spheroidal side —
the same objects as the Q3 mainline (Weil positivity, prolate layer on this bus:
ProlateLayer.lean, goals 016/019/020).

## The paper's own missing steps (§8, verbatim summary)

1. To apply Theorem 5.10 to QW_λ one must PROVE that its smallest eigenvalue
   (existence by their Theorem 3.6) is SIMPLE and its eigenvector ξ_λ is EVEN.
2. Establish that k_λ approximates (a scalar multiple of) ξ_λ accurately enough to
   justify convergence of the zeros of ξ̂_λ to the nontrivial zeros of ζ(1/2 + is).

Supporting indications named by the authors: simple-even holds for the prolate-wave
operator PW_λ for all λ; the tiny eigenvalues ε_λ match the P_λ/P̂_λ discrepancy;
numerical proximity k_λ ≈ ξ_λ extends to higher eigenfunctions.

## Cross-links for the promotion card (Mythos)

- Their QW_λ = Weil quadratic form ↔ Q3 Weil positivity core (Weil_criterion_tau0).
- Their prolate approximation ↔ bus prolate layer (goals 016/019/020, ProlateLayer.lean).
- Their "simple + even smallest eigenvalue" gap ↔ candidate NEW named lemma for the
  S2 cluster / H2b wall — this is the exact statement the mainline import needs.
- Numerical spectra ≈ zeta zeros = evidence, not proof (their own wording); no
  status promotion follows from this import.
═══ FILE END: THM510: docs/routeB_bus/imports/THM510_ZETA_SPECTRAL_TRIPLES_2026-07-31.md ═══

═══ FILE BEGIN: CONTRACT: q3.lean.aristotle/docs/ROUTE_B_THEOREM_CONTRACT_v2.md ═══
# ROUTE B — THEOREM CONTRACT v2 (исправленный финальный контракт Новой дороги)

Дата: 2026-07-10 (поздняя ревизия) · Автор: Mythos · Ревизия по read-only плану Codex (принят с одной арифметической поправкой, см. §3).
Статус: contract — целевая теорема + реестр обязательств; НЕ утверждение о доказанности. Подчинён `ROUTE_B_STATE.md` + `loop_state.json`. NOT_RH.
Маршрут: `ALPHA_ROUTE_REMAINS_CHALLENGER`; Старая дорога (T0-pd → H-bridge) не затрагивается; смешивание цепей запрещено.
Заменяет: `docs/ROUTE_B_THEOREM_CONTRACT_v1.md` (помечен SUPERSEDED).

---

## 1. Δ против v1 (восемь ремонтов — для контрподписи голом 008)

1. H4 заменён на **QuantitativeSafeWitness** с явной степенной арифметикой (§3).
2. **SafeAlphaUpper оценивает каноническую α, а не μ₁**; связка α ↔ a₁ — доказываемый crosswalk, не определение.
3. Финальный экспорт — ТОЛЬКО через ZEO 2.2; узел 2.1 — независимая перекрёстная проверка вне главной цепи.
4. Введён режим конечной размерности: **N = N(λ) либо явная лемма конечно-континуального моста**; все спектральные объекты несут N в типе.
5. **PO-11 (ZEOExportSoundness) получает статус OPEN_CRITICAL** и поднимается до уровня 1: пока стрелка «Dictionary ∧ Witness ⟹ нули Ξ вещественны» не разбита на конечные леммы, тяжёлые перья не покупаются.
6. Ранний **SAFE feasibility gate** (аудит theorem-shapes пяти листьев) — до уравнения хвоста.
7. Зонд переименован: r₁₃ → **rGap13**; зафиксирована коллизия имён с локальным r1 = θ₁/λ₁(G_even) ≈ 9.51e−32 — это РАЗНЫЕ объекты; 50-порядковый судья НЕДЕЙСТВИТЕЛЕН до source audit. Наблюдённое μ₁/(μ₃−μ₁) ≈ 2.66e−8 — PROVISIONAL_COINCIDENCE_SIGNAL (в полосе coincidence-сценария), провенанс не заверен.
8. Степенная арифметика ИСПРАВЛЕНА: строгое условие **rΔ − rα > 2q_b + 1** (в read-only плане пропущен вклад явного множителя λ; поправка +1).

## 2. Словарь H0 — ExactDetectorDictionary (тип гипотезы)

Обязательные строки (расширение A1–A8):
- единственная каноническая **α(λ) ≥ 0**, выбранная из существующих реализаций {raw, projected, opt} с доказанным crosswalk к каноническому a₁ = s_λ²·QW(g_λ);
- α ≥ 0 — следствием min–max/Rayleigh-структуры, НЕ численного знака;
- **Δe(λ) := μ₃(λ) − μ₁(λ) > 0 строго** (кратности исключены леммой), same-parity выбор доказан; trial-вектор живёт в том же чётном секторе;
- оператор M_λ: матрица, пространство, базис, Gram-конвенция, зависимость от N; режим N = N(λ) или мост в континуум;
- **b(λ)**: формула + двусторонняя граница 0 < c_b ≤ |b(λ)|·λ^(−q_b) ≤ C_b на Λ;
- детектор: W′(λ)² = |b(λ)|²·λ·α(λ)/Δe(λ);
- квантор: кофинальная Λ = {λ : λ² ∈ ℕ} (достаточность для liminf доказана; для контуров Руше — PO-11).

## 3. Центральная количественная лемма (QuantitativeSafeWitness)

Пусть на Λ:
```text
|b(λ)| ≤ C_b·λ^(q_b)
0 ≤ α(λ) ≤ C_α·λ^(r_α)·e^(−4πλ²)      [SafeAlphaUpper]
Δe(λ) ≥ c_Δ·λ^(r_Δ)·e^(−4πλ²)          [SafeGapLower]
```
Тогда
```text
W′(λ) ≤ C·λ^( q_b + (1 + r_α − r_Δ)/2 ).
```
Строгое достаточное условие W′ → 0 на Λ:
```text
r_Δ − r_α > 2·q_b + 1        (запас δ := r_Δ − r_α − 2q_b − 1 > 0 фиксируется явно)
```
Поправка к read-only плану: множитель λ в W′² даёт «+1»; условие «r_Δ − r_α > 2q_b» недостаточно на границе.

## 4. Цепь вывода (форма финальной сборки; каждая стрелка — отдельная теорема)

```text
H0 (словарь, §2)
Supply-цепь: ProjectedProlateDefectEquation → Gate 6 (6A–6D)
   → G04DefectGramBridge / узел 3.3 (B* ≤ 25) → G3a → DetectorBridge
   → SafeAlphaUpper (финальная форма: 0 ≤ α ≤ C_α λ^{r_α} e^{−4πλ²})
Parity-clean spectral theorem → SafeGapLower
SafeSignAndB (α ≥ 0 структурно; Δe > 0 строго; b двусторонне)
SafeRateAssembly (r_Δ − r_α > 2q_b + 1, запас δ > 0)
   ⟹ QuantitativeSafeWitness: ∃ λ_j ∈ Λ, λ_j → ∞, W′(λ_j) → 0
ZEOSoundness (PO-11): локально-равномерная сходимость нормированных
   конечных функций; контуры Руше на дискретной Λ; отсутствие escaping
   zeros; невырожденность b; точная идентификация предельной Ξ
   ⟹ все нули Ξ вещественны
XiRealIffRH ⟹ RH.
```
DetectorBridge обязан ЗАКАНЧИВАТЬСЯ оценкой α в форме SafeAlphaUpper (или точной промежуточной, из которой она следует отдельной леммой) — абстрактного E_spec недостаточно.

## 5. Вердикт нециркулярности сейфа (перенос из v1, в силе)

`SAFE_MECHANISM_CANDIDATE_NAMED`. Готовой безусловной теоремы для листьев нет; ДОКАЗАНО (OBJECT_LOCK §3), что определительного моста α ≤ κ_λ|a₁| с субэкспоненциальным κ не существует — сейф нерезервируем внутри G3a. Кандидат-механизм листа SafeGapLower: возмущение против полиномиально разделённой Fuchs-диагонали (Вейль/Дэвис–Кахан); входы безусловны. Самая вероятная стена всей дороги — **SafeGapLower** (совпадающий диагноз Mythos + Codex). Перевороты вердикта — как в v1 §5.

## 6. Анти-циркулярные статьи (без изменений против v1)

Эпистемический файрвол (BFM запрещён; Гонек/twisted — замены); K7 (вычисление не занимает квантор); запрет tau0-подмены (`docs/trackB/WEIL_SQUARE_CLASS_SPEC.md`); классификация импортов THEOREM/CONDITIONAL/CONJECTURE/HEURISTIC с sha-сверкой.

## 7. Реестр обязательств v2 (уровни; внутри уровня — любой порядок)

```text
УРОВЕНЬ 0 (ZERO compute / контрольная плоскость)
PO-0  Contract v2 crosscheck + синхронизация STATE↔loop + провенанс
      источников (вкл. rGap13 source audit и физическое размещение
      ALPHA_DEMAND_AUDIT / OBJECT_LOCK)                [гол 008, Codex]
УРОВЕНЬ 1 (kill-гейты до тяжёлой аналитики)
PO-1  Словарь H0 (§2): выбор канонической α, crosswalk, N-режим,
      строгая щель, b двусторонне                      [перо M → гейт C]
PO-2  Чётность: ParityLeakSourceAudit → ParityProjectedOperatorLock;
      до PASS запрещены аргументы от W′/gap/rGap13     [гейты C]
PO-11 ZEOExportSoundness (OPEN_CRITICAL): стрелка Witness ⟹ Ξ-real
      разбита на конечные леммы; коды провала:
      ROUCHE_QUANTIFIER_GAP / XI_LIMIT_IDENTIFICATION_GAP /
      FINITE_TO_UNIVERSAL_GAP / ZEO_EXPORT_NOT_DERIVED [перо M + Sol]
PO-12a SAFE feasibility: theorem-shapes пяти листьев
      (AlphaUpper/GapLower/BUpper/Sign/Rate); после чётности —
      дешёвый falsifier (может убить, не может доказать)
      PASS: SAFE_RATE_SHAPE_LOCKED, SAFE_CANDIDATE_SURVIVES_FALSIFIER
      KILL: SAFE_*_NO_SOURCE / SAFE_IS_RH_REPACKAGING  [перо M + гейт C]
УРОВЕНЬ 2 (только после уровня 1)
PO-3  ProjectedProlateDefectEquation (bulk + коммутатор + граница +
      полюс + середина; статусы каналов; 007-факты фиксированы:
      C_mid PRESENT_EXACT, C_pole PRESENT_EXACT, C_right ABSENT) [перо M]
PO-4..6  Gate 6A/6B/6C отдельными голами; един X_λ; выход обязан
      кормить SafeAlphaUpper; kill: G3_NORMALIZED_DEFECT_MATRIX_
      POLY_BOUND_FATAL                                  [перо M + гейты C]
PO-7  Гейты 3–5 (radical-window, Poisson-факторизация, ε↓0)   [перо M]
PO-8  Узел 3.3: Rayleigh/Gram-мост, B* ≤ 25; STOP-коды:
      RAYLEIGH_BRIDGE_NOT_DERIVED / UNIT_LEDGER_MISMATCH /
      BUDGET_25_EXCEEDED / CHANNEL_STATUS_UNCLASSIFIED  [перо M + гейт C]
PO-9  Сборка G3a единым леджером (шаблон 007)           [перо M + гейт C]
PO-10 DetectorBridge → финальная форма SafeAlphaUpper   [перо M + Sol]
УРОВЕНЬ 3 (сейф)
PO-12 Четыре листа: SafeAlphaUpper, SafeGapLower, SafeSignAndB,
      SafeRateAssembly → QuantitativeSafeWitness        [все каналы]
УРОВЕНЬ 4
PO-13 Lean: request-local definitions/signatures module (не импортируется
      в Q3.Main); один sorry = один адрес обязательства; закрытие тел
      после self-attack + Прошка + source audit + falsifier;
      `lake env lean` после каждого узла; скан sorry|admit|exact?;
      check_axioms; приёмка: zero sorry, zero unexpected axioms,
      zero tau0, zero RH-conditional imports, один объект в статье
      и в Lean                                          [C]
```

Закрыто к дате v2: 6D; Λ-достаточность для liminf; нерезервируемость сейфа (O2); шаблон точного леджера (007, 2.2e−89); ядро словаря G3_0; кросс-подтверждение H2-ветки (006-G1 ↔ G3_0).

## 8. Условия расторжения (расширены)

(а) SAFE_IS_RH_REPACKAGING доказан; (б) SAFE_GAP_LOWER_NO_SOURCE после честного feasibility-аудита и falsifier; (в) G3_NORMALIZED_DEFECT_MATRIX_POLY_BOUND_FATAL; (г) ZEO_EXPORT_NOT_DERIVED неремонтируем. Резервы: Route C «pair, don't multiply»; Cayley–Li Orbifold detector.

## 9. Приёмка

Контракт исполнен ⟺ PO-0…PO-13 закрыты в порядке уровней и `#print axioms` финального экспорта чист. До этого: RH — OPEN; тяжёлые перья уровня 2 не покупаются, пока уровень 1 не PASS.
═══ FILE END: CONTRACT: q3.lean.aristotle/docs/ROUTE_B_THEOREM_CONTRACT_v2.md ═══

═══ FILE BEGIN: GOAL043: docs/routeB_bus/043_muntz_v3_supplier_hrm.goal.md ═══
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
═══ FILE END: GOAL043: docs/routeB_bus/043_muntz_v3_supplier_hrm.goal.md ═══

