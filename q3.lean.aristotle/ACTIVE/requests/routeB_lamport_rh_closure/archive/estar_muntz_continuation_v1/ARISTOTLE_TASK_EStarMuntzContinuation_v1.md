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
