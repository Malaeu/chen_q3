TASK:
EStarMuntzZeroMassContinuation_Standalone_v3_PoleSubtracted

CONTEXT (one line):
Self-contained: Mathlib only, no project files. REPLACES the stale
EStarMuntzContinuation_Standalone (v1): its T4 asked for analyticity of the
RAW product w ↦ ζ(w)·Mellin h w through w = 1, which is FALSE whenever
deriv (Mellin h) 1 ≠ 0 (zero mass gives Mellin h 1 = 0, so the raw point
value is 0, while the removable value of the punctured product is
deriv (Mellin h) 1). Keep all green T1–T3 work and the locally reverified
boundary-cell bridge; rebuild only the zeta layer (old T4/T5) around a
pole-subtracted analytic continuation. Integration happens elsewhere, offline.

SETUP (define inside the file; aligned with RiemannBoundaryCellBridge
hypotheses — if a local v2 hypothesis block already exists, keep it and
replace only the T4/T5 layer; the mathematical content below may not drift):
  variables (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (K : NNReal)
  (hsupp : ∀ v, v ∉ Set.Icc (0:ℝ) b → h v = 0)
  (hlip : LipschitzOnWith K h (Set.Ico (0:ℝ) b))
  (hmeas : Measurable h)
  (hmass : ∫ v in Set.Ioi (0:ℝ), h v = 0)
  (Λ : ℝ) (hΛ : 1 ≤ Λ)

  noncomputable def Estar (h : ℝ → ℂ) (u : ℝ) : ℂ :=
    Real.sqrt u * ∑' n : ℕ+, h (n * u)

  noncomputable def Mellin (k : ℝ → ℂ) (s : ℂ) : ℂ :=
    ∫ u in Set.Ioi (0:ℝ), k u * (u : ℂ) ^ (s - 1)

  noncomputable def Gwin (s : ℂ) : ℂ :=
    ∫ u in Set.Ioo (Λ⁻¹) Λ, Estar h u * (u : ℂ) ^ (s - 1)
  noncomputable def Rminus (s : ℂ) : ℂ :=
    ∫ u in Set.Ioo (0:ℝ) (Λ⁻¹), Estar h u * (u : ℂ) ^ (s - 1)
  noncomputable def Rplus (s : ℂ) : ℂ :=
    ∫ u in Set.Ioi Λ, Estar h u * (u : ℂ) ^ (s - 1)

  def H : Set ℂ := {w : ℂ | 0 < w.re}

NEW DEFINITIONS (the pole-subtracted layer):

  -- 1. Mellin zero quotient (Mathlib's derivative-corrected slope)
  noncomputable def MellinDivOne (w : ℂ) : ℂ :=
    dslope (Mellin h) 1 w

  -- 2. Residue-removed zeta factor (an analytic extension, NOT the raw value)
  noncomputable def ZetaResidueFactor (w : ℂ) : ℂ :=
    Function.update (fun z => (z - 1) * riemannZeta z) 1 1

  -- 3. Pole-subtracted product
  noncomputable def ZetaMellinPoleSub (w : ℂ) : ℂ :=
    ZetaResidueFactor w * MellinDivOne h w

  If the explicit Function.update definition causes avoidable API friction,
  an existential analytic witness is permitted INSTEAD of def 2:
    ∃ Z1, AnalyticOnNhd ℂ Z1 H ∧ Z1 1 = 1 ∧
          ∀ w ∈ H, w ≠ 1 → Z1 w = (w - 1) * riemannZeta w
  Do not weaken the mathematical content.

TARGET DECLARATIONS (all with no sorry):

T4a: Mellin h is analytic on H (AnalyticOnNhd ℂ (Mellin h) H).
     (Support in [0,b] with h bounded there: ‖h‖ ≤ ‖h 0‖ + K·b on [0,b) and
      ‖h b‖ at the endpoint; the integral over (0,b] converges locally
      uniformly for 0 < Re w — differentiation under the integral or Morera.)

T4b: Mellin h 1 = 0.   (= hmass, after rpow simplification at s = 1.)

T4c: MellinDivOne h is analytic on H, with the identities
     MellinDivOne h 1 = deriv (Mellin h) 1;
     w ≠ 1 → MellinDivOne h w = (Mellin h w - Mellin h 1) / (w - 1);
     hmass → w ≠ 1 → MellinDivOne h w = Mellin h w / (w - 1).
     (At w = 1 use the analytic dslope power-series theorem; away from 1
      the ordinary quotient formula.)

T4d: ZetaResidueFactor is analytic on H, with
     ZetaResidueFactor 1 = 1;
     w ≠ 1 → ZetaResidueFactor w = (w - 1) * riemannZeta w.
     (At w = 1: riemannZeta_residue_one for continuity of the updated
      factor; differentiability of ζ on the punctured neighborhood;
      removable-singularity theorem.)

T4e: ZetaMellinPoleSub h is analytic on H
     (zetaMellinPoleSub_analyticOn : AnalyticOnNhd ℂ (ZetaMellinPoleSub h) H).

T4f (off-pole equality): w ∈ H → w ≠ 1 →
     ZetaMellinPoleSub h w = riemannZeta w * Mellin h w.

T4g (pole value): ZetaMellinPoleSub h 1 = deriv (Mellin h) 1.
     NO theorem may identify this value with the raw Mathlib expression
     riemannZeta 1 * Mellin h 1.

T5 (MAIN — continued window identity): given the absolute-region identity
   as a hypothesis
   (habs : ∀ s : ℂ, 1/2 < s.re →
      Gwin s = riemannZeta (s + 1/2) * Mellin h (s + 1/2) - Rminus s - Rplus s),
   conclude
      ∀ s : ℂ, -1/2 < s.re →
      Gwin s = ZetaMellinPoleSub h (s + 1/2) - Rminus s - Rplus s.
   Route: Gwin entire (compact window, integrable bound); Rplus entire (T1,
   retained); Rminus analytic on Re s > -1/2 (T3, retained); T4e makes the
   right side analytic on the connected open half-plane {Re s > -1/2};
   both sides agree on {Re s > 1/2} by habs and T4f (s + 1/2 ≠ 1 there
   ⇔ s ≠ 1/2, and Re s > 1/2 excludes s = 1/2... careful: s = 1/2 has
   Re s = 1/2, not > 1/2, so the open agreement region is safe); apply the
   identity theorem (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq or
   the pinned-Mathlib equivalent).

T5-cor-1 (raw-product corollary, punctured only): for -1/2 < Re s, s ≠ 1/2:
   Gwin s = riemannZeta (s + 1/2) * Mellin h (s + 1/2) - Rminus s - Rplus s.
   (T5 + T4f. The raw product corollary DOMAIN IS w ≠ 1 only.)

T5-cor-2 (pole-value corollary — the theorem that replaces the false raw
   pointwise statement):
   Gwin (1/2) = deriv (Mellin h) 1 - Rminus (1/2) - Rplus (1/2).
   (T5 at s = 1/2 + T4g.)

PLANTS (zero mass and the pole subtraction are both load-bearing):

PL1 (mass-carrying source): for an explicit triangular bump h₀ ≥ 0
   supported in [1,2] with ∫ h₀ ≠ 0, the bounded-sums conclusion of the
   retained T2 FAILS: exhibit a quantitative lower bound along u = 1/k
   showing ∑' n, h₀(n·u) grows like (∫h₀)/u, hence Estar h₀ u ≳ u^{-1/2}.
   No smallness talk; a lower bound along a sequence suffices.

PL2 (raw value mismatch): for an explicit zero-mass difference of
   triangular bumps h₁ (positive bump supported in [1,2], negative bump
   supported in [2,4], equal unit masses — so ∫ h₁ = 0 and
   deriv (Mellin h₁) 1 = ∫ h₁(u)·ln u du < 0 by strict monotonicity of ln
   between the two supports), prove:
     ZetaMellinPoleSub h₁ 1 = deriv (Mellin h₁) 1 ≠ 0
   and
     ¬ ContinuousAt (fun w => riemannZeta w * Mellin h₁ w) 1
   (the raw product's point value is riemannZeta 1 * 0 = 0 while its limit
   along w → 1, w ≠ 1 is deriv (Mellin h₁) 1 ≠ 0). This plant rejects any
   attempt to reinstate the v1 raw-product T4.

PL3 (factor cancellation — mutants must fail): assume, for contradiction,
   a mutated off-pole identity on all of H \ {1}:
   (mutant 1, drop (w-1) from the zeta factor)
     ∀ w ∈ H, w ≠ 1 → riemannZeta w * MellinDivOne h₁ w
                        = riemannZeta w * Mellin h₁ w
   (mutant 2, drop the division from the Mellin factor)
     ∀ w ∈ H, w ≠ 1 → ((w-1) * riemannZeta w) * Mellin h₁ w
                        = riemannZeta w * Mellin h₁ w.
   Show each forces (identity theorem on the connected H: ζ ≢ 0, the
   linear factor ≢ 0) Mellin h₁ ≡ 0 on H, contradicting PL2's
   deriv (Mellin h₁) 1 ≠ 0. Hence both mutated equalities are false:
   the pole subtraction is exact, not decorative.

IMPORTS / EXPECTED MATHLIB API:
  Mathlib.Analysis.Calculus.DSlope
  Mathlib.Analysis.Analytic.IsolatedZeros
  Mathlib.Analysis.Complex.RemovableSingularity
  Mathlib.NumberTheory.LSeries.RiemannZeta
Expected key API:
  dslope, dslope_same (dslope f a a = deriv f a),
  HasFPowerSeriesAt.has_fpower_series_dslope_fslope,
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt,
  riemannZeta_residue_one, differentiableAt_riemannZeta,
  AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
Exact theorem names may be adapted to the pinned Mathlib version, but the
target semantics may not drift.

FORBIDDEN:
- no raw ζ·Mellin value at w = 1 anywhere in the chain: no theorem may
  assert continuity or differentiability of the RAW product at w = 1, and
  no theorem may identify ZetaMellinPoleSub h 1 with
  riemannZeta 1 * Mellin h 1;
- no replacement of the removable value by 0;
- no global Lipschitz assumption on the zero extension (the intended h
  jumps at b; Lipschitz is on Ico 0 b only);
- no claim that Mellin h is entire (support reaches 0: analytic on H only);
- no new axioms, no sorry/admit, no native_decide;
- no RH or zeta-zero input; no STATE mutation;
- import Mathlib only; no external project names.

VALIDATION:
- lake env lean <touched-file>; lake build;
- grep sorry/admit/axiom/native_decide: clean;
- #print axioms for: the MellinDivOne analyticity theorem, the
  ZetaResidueFactor analyticity theorem, the ZetaMellinPoleSub analyticity
  theorem, the continued window identity (T5), the punctured raw corollary,
  the pole-value corollary, PL1, PL2, PL3:
  exactly [propext, Classical.choice, Quot.sound];
- report which Mathlib lemmas supplied (i) the dslope analyticity step,
  (ii) the removable-singularity step at w = 1, (iii) the identity theorem.

RETURN EXACTLY ONE PRIMARY STATUS:
ESTAR_MUNTZ_POLE_SUBTRACTED_CONTINUATION_PROVED
MELLIN_DSLOPE_ANALYTICITY_GAP (name the exact missing Mathlib statement)
ZETA_RESIDUE_FACTOR_EXTENSION_GAP (name it)
IDENTITY_THEOREM_GLUE_GAP (name it)
RIEMANN_SUM_BOUNDARY_CELL_GAP (name it)
Do NOT return the vague v1 code ZETA_POLE_API_GAP: the repaired contract
separates the two genuine API fronts (dslope layer vs residue-factor layer).
