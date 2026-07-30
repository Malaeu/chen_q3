TASK:
EdgeSliverMomentReduction_Standalone

CONTEXT (one line):
Self-contained: Mathlib only, no project files. Transaction 034 reduced a
cofinal positive-part moment bound to one abstract inequality: a measurable
real function that is a.e. nonpositive outside a left edge sliver and
boundary-cell bounded inside it has its weighted positive-part moment
controlled by one explicit closed form. Prove exactly that inequality and
its guards in a fresh file. Integration (with the already proved
RiemannBoundaryCellBridge supplying the |E| ≤ B·√u hypothesis, and with the
sign supplier) happens elsewhere, offline.

SETUP (define inside the file):
  variables (E : ℝ → ℝ) (lam A B σ : ℝ)
  (hlam : 1 ≤ lam) (hA1 : 1 ≤ A) (hAlam : A ≤ lam) (hB : 0 ≤ B)
  (hσ0 : 0 ≤ σ) (hσ : σ < 1/2)
  (hmeas : Measurable E)
  (hsign : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioc (A/lam) lam)),
             E u ≤ 0)
  (hbridge : ∀ u ∈ Set.Ioo (0:ℝ) 1, |E u| ≤ B * Real.sqrt u)

  noncomputable def edgeMoment (E : ℝ → ℝ) (lam σ : ℝ) : ℝ :=
    ∫ u in Set.Ioc (lam⁻¹) lam, max (E u) 0 * u ^ (-σ - 1)
  -- u ^ (·) is Real.rpow throughout; every u in the domain is > 0.
  -- max (E u) 0 * u ^ (-σ-1) is the contract integrand max(E,0)·u^{-σ}·du/u.

TARGETS (no sorry):

T0 (geometry + integrand control on the sliver):
   (a) 0 < lam⁻¹, lam⁻¹ ≤ A/lam, A/lam ≤ 1, A/lam ≤ lam
       (from 1 ≤ A ≤ lam ≤ lam^2; note A/lam ≤ 1 ⇔ A ≤ lam).
   (b) for u ∈ Set.Ioo (lam⁻¹) (A/lam) (an open subinterval of Ioo 0 1),
       max (E u) 0 * u ^ (-σ - 1) ≤ B * u ^ (-σ - 1/2 : ℝ).
       (Combine max_le, hbridge, Real.sqrt_eq_rpow, and
        Real.rpow_natCast/rpow_add for u > 0.)
   If A = lam the sliver's right endpoint touches 1 where hbridge is not
   assumed; this is a single point of measure zero — work on Ioo/Ioc so it
   never enters.

T1 (sliver bound):
   ∫ u in Set.Ioc (lam⁻¹) (A/lam), max (E u) 0 * u ^ (-σ - 1)
     ≤ B * lam ^ (σ - 1/2) * (A ^ ((1:ℝ)/2 - σ) - 1) / (1/2 - σ).
   Route: monotonicity of the set integral against the majorant of T0(b)
   (both sides integrable: the majorant is continuous on a compact
   closure; the integrand is measurable, nonnegative, dominated), then the
   exact rpow integral
     ∫ u in Set.Ioc (lam⁻¹) (A/lam), u ^ (-σ - 1/2 : ℝ)
       = ((A/lam) ^ ((1:ℝ)/2 - σ) - (lam⁻¹) ^ ((1:ℝ)/2 - σ)) / (1/2 - σ)
   (exponent -σ-1/2 ≠ -1 since 1/2 - σ > 0; use
    intervalIntegral.integral_rpow via integral_Ioc_eq_intervalIntegral, or
    the set-integral rpow lemma of the pinned Mathlib), and the algebra
     (A/lam)^{1/2-σ} = A^{1/2-σ} * lam^{σ-1/2},  (lam⁻¹)^{1/2-σ} = lam^{σ-1/2}
   (Real.div_rpow / Real.inv_rpow / Real.rpow_neg with lam > 0, A > 0).

T2 (outer vanish):
   ∫ u in Set.Ioc (A/lam) lam, max (E u) 0 * u ^ (-σ - 1) = 0.
   Route: by hsign the integrand is 0 a.e. on the restricted measure
   (max (E u) 0 = 0 when E u ≤ 0), so the integral vanishes
   (MeasureTheory.setIntegral_congr_ae to the zero function, or
    integral_eq_zero_of_ae).

T3 (MAIN — the named reduction, verbatim constant):
   edgeMoment E lam σ
     ≤ B * lam ^ (σ - 1/2) * (A ^ ((1:ℝ)/2 - σ) - 1) / (1/2 - σ).
   Route: Set.Ioc (lam⁻¹) lam = Set.Ioc (lam⁻¹) (A/lam) ∪ Set.Ioc (A/lam) lam
   (disjoint, since lam⁻¹ ≤ A/lam ≤ lam by T0(a)); split the set integral
   (integrability on each piece: T1's domination on the sliver, a.e.-zero
   on the outer piece), then T1 + T2.

T4 (guards):
   T4a (RHS sanity): 0 ≤ B * lam ^ (σ - 1/2) * (A ^ ((1:ℝ)/2 - σ) - 1) / (1/2 - σ)
       (A ≥ 1 and 1/2 - σ > 0 give A ^ (1/2-σ) ≥ 1).
   T4b (degenerate sliver): A = 1 → edgeMoment E lam σ = 0
       (RHS = 0 by rpow_zero-type simp... careful: A = 1 gives A^{1/2-σ} = 1
        so RHS = 0; combine T3 with integral_nonneg of the nonnegative
        integrand to force equality with 0).
   T4c (sharpness witness — the E0-identity; the constant is optimal):
       define E0 : ℝ → ℝ := fun u => if u < A/lam then B * Real.sqrt u else 0.
       Prove E0 satisfies hmeas, hsign, hbridge, and
       edgeMoment E0 lam σ
         = B * lam ^ (σ - 1/2) * (A ^ ((1:ℝ)/2 - σ) - 1) / (1/2 - σ).
       (On the sliver max (E0 u) 0 = B * √u exactly; the integral is the
        same rpow integral as in T1 with equality; outside, 0.)

FORBIDDEN:
- no new axioms, no native_decide, no sorry/admit;
- import Mathlib only; no external project names;
- do not strengthen hsign to pointwise ∀ u (the supplier provides a.e. only);
- do not weaken the explicit constant to an unnamed ∃ C (the closed form is
  the point; it is consumed with A := 4/3 downstream);
- do not add the case σ = 1/2 or A < 1 (out of contract);
- do not assume E integrable globally — integrability must come out of the
  hypotheses exactly as in T1/T2/T3.

VALIDATION:
- lake build succeeds; #print axioms for T0–T4c:
  exactly [propext, Classical.choice, Quot.sound];
- grep sorry/admit/axiom/native_decide: clean;
- report which Mathlib lemmas supplied (i) the rpow integral over an
  interval, (ii) the disjoint set-integral splitting, (iii) the
  a.e.-vanishing integral on the outer piece.

RETURN EXACTLY ONE PRIMARY STATUS:
EDGE_SLIVER_MOMENT_REDUCTION_PROVED
RPOW_INTERVAL_INTEGRAL_API_GAP (name the exact missing Mathlib statement)
SET_INTEGRAL_SPLIT_API_GAP (name it)
POSPART_AE_VANISH_API_GAP (name it)
