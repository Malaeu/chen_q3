import Q3.Proofs.RouteB.G6N1Satz9SourcePackageInterface

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set Filter

namespace Q3.RouteB.D0Pstar

/-!
# F72.1A0 — the center-normalized Satz-9 rate transfer

Floor `F72_1A0_CENTER_NORMALIZED_RATE_TRANSFER` of verdict `a0b787db`.

The book asymptotic is external mathematics: a citation is not a kernel term,
and neither reproving the book nor adding a project axiom is allowed.  What is
kernel-executable is the nontrivial part the route maps kept using silently:
a raw uniform rate on an exactly scaled source mode survives centre
normalization **only** under an explicit denominator guard, and the exact
bandwidth identity `gamma = 2*pi*lambda^2` converts the `gamma^(-1)` rate into
the physical `lambda^(-2)` rate with an exact constant, not a fitted one.

The private plant shows the guard is load-bearing: a raw error of size one
can be amplified past ten by centre normalization when the centre value is
small.  The theorem is generic in the fixed mode; the raw paper rate and the
paper scale remain explicit inputs about the same `S` and are never inferred
from the payload type.

LEDGER:
  CLOSES: [F72_1A_CENTER_NORMALIZATION_DENOMINATOR_LEDGER,
           F72_1A_GAMMA_TO_LAMBDA_SQUARED_RATE_TRANSFER]
  OPENS:  []
-/

/-- **The plant.**  A raw approximation with error one at two points, whose
centre-normalized view is off by more than ten: centre normalization can
amplify a uniform error by two orders of magnitude when the centre value is
small.  The denominator guard in the transfer theorem is load-bearing. -/
private theorem centerNormalization_denominator_guard_plant :
    |(1 / 100 : ℝ) - 1| ≤ 1 ∧
      |(1 : ℝ) - 1| ≤ 1 ∧
      |(1 : ℝ) / (1 / 100 : ℝ) - 1| > 10 := by
  norm_num

/-- **F72.1A0.**  A raw uniform rate `rawC / gamma` on the exactly scaled
source mode, together with the denominator guard `2 * rawC / gamma ≤ centre`,
transfers to the centre-normalized view at the physical rate
`lambda^(-2)` with the exact constant `rawC * (centre + bound) / (pi * centre)`. -/
theorem centerNormalizedSatz9Rate_of_scaledFixedModeRate
    (lambda gamma theta : ℕ → ℝ)
    (S : ∀ k, Satz9SourceData (lambda k) (theta k))
    (scale : ℕ → ℂ)
    (target : ℝ → ℂ)
    (targetCenter targetBound rawC : ℝ)
    (hlambda : ∀ k, 0 < lambda k)
    (hgamma : ∀ k,
      gamma k = 2 * Real.pi * (lambda k) ^ 2)
    (hcenter : target 0 = (targetCenter : ℂ))
    (hcenterPos : 0 < targetCenter)
    (hbound : 0 ≤ targetBound)
    (htarget : ∀ x : ℝ, ‖target x‖ ≤ targetBound)
    (hrawC : 0 ≤ rawC)
    (hscale : ∀ k, scale k ≠ 0)
    (hraw :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(lambda k)) (lambda k),
          ‖scale k * (S k).p x - target x‖ ≤ rawC / gamma k)
    (hdenom :
      ∀ᶠ k in Filter.atTop,
        2 * (rawC / gamma k) ≤ targetCenter) :
    ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(lambda k)) (lambda k),
        ‖(targetCenter : ℂ) * centerNormalized (S k).p x - target x‖ ≤
          (rawC * (targetCenter + targetBound) /
            (Real.pi * targetCenter)) / (lambda k) ^ 2 := by
  filter_upwards [hraw, hdenom] with k hrawk hdenomk
  intro x hx
  have hlk := hlambda k
  have hgk : 0 < gamma k := by
    rw [hgamma k]
    positivity
  set eps : ℝ := rawC / gamma k with hepsdef
  have heps0 : 0 ≤ eps := by positivity
  have h0mem : (0 : ℝ) ∈ Set.Icc (-(lambda k)) (lambda k) :=
    ⟨by linarith, by linarith⟩
  set q : ℝ → ℂ := fun y => scale k * (S k).p y with hqdef
  have hq0close : ‖q 0 - target 0‖ ≤ eps := hrawk 0 h0mem
  have hcnorm : ‖target 0‖ = targetCenter := by
    rw [hcenter, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcenterPos]
  have hq0lower : targetCenter - eps ≤ ‖q 0‖ := by
    have h1 : ‖target 0‖ - ‖q 0‖ ≤ ‖target 0 - q 0‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at h1
    rw [hcnorm] at h1
    linarith [hq0close]
  have hhalf : targetCenter / 2 ≤ ‖q 0‖ := by
    linarith [hdenomk]
  have hq0pos : 0 < ‖q 0‖ := lt_of_lt_of_le (by linarith) hhalf
  have hq0ne : q 0 ≠ 0 := norm_pos_iff.mp hq0pos
  -- the centre-normalized view through the scaled function
  have hratio : centerNormalized (S k).p x = q x / q 0 := by
    rw [centerNormalized, hqdef]
    rw [mul_div_mul_left _ _ (hscale k)]
  -- the exact numerator identity
  have hidentity :
      (targetCenter : ℂ) * (q x / q 0) - target x
        = ((targetCenter : ℂ) * (q x - target x)
            + target x * ((targetCenter : ℂ) - q 0)) / q 0 := by
    field_simp
    ring
  rw [hratio, hidentity]
  -- numerator bound
  have hnum1 : ‖(targetCenter : ℂ) * (q x - target x)‖ ≤ targetCenter * eps := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcenterPos]
    exact mul_le_mul_of_nonneg_left (hrawk x hx) (le_of_lt hcenterPos)
  have hnum2 : ‖target x * ((targetCenter : ℂ) - q 0)‖ ≤ targetBound * eps := by
    rw [norm_mul]
    have h2 : ‖(targetCenter : ℂ) - q 0‖ ≤ eps := by
      rw [← hcenter, norm_sub_rev]
      exact hq0close
    exact mul_le_mul (htarget x) h2 (norm_nonneg _) hbound
  have hnum : ‖(targetCenter : ℂ) * (q x - target x)
      + target x * ((targetCenter : ℂ) - q 0)‖
        ≤ (targetCenter + targetBound) * eps :=
    le_trans (norm_add_le _ _) (by linarith [hnum1, hnum2])
  -- divide by the guarded denominator
  have hdivbound :
      ‖((targetCenter : ℂ) * (q x - target x)
          + target x * ((targetCenter : ℂ) - q 0)) / q 0‖
        ≤ ((targetCenter + targetBound) * eps) / (targetCenter / 2) := by
    rw [norm_div]
    apply div_le_div₀ (by positivity) hnum (by positivity) hhalf
  refine le_trans hdivbound (le_of_eq ?_)
  -- the exact constant: gamma = 2*pi*lambda^2 turns eps into the lambda^(-2) rate
  rw [hepsdef, hgamma k]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp

#print axioms centerNormalizedSatz9Rate_of_scaledFixedModeRate

end Q3.RouteB.D0Pstar
