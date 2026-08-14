import Q3.Proofs.RouteB.D0Mode4SchurRootQuadraticCrossing

/-!
# Inertia labels strictly order the exact mode-four Schur roots

Knowledge preflight for `Goal058.G3.Mode4SchurRootInertiaLabel` used the exact
shelf queries `Goal058 Schur root inertia label negativeCount uniqueness`,
`mode4RootFunction distinct roots negative eigenvalue count`, and
`ordered PSWF root Schur inertia index selection`.  The search found the exact
root function, simple-root kernel, and one-direction negative-index jump, but
no theorem identifying the order of two roots with the order of their inertia
labels.

This file composes those existing exact facts.  On the pole-free source domain,
the negative-eigenvalue count is a strict order embedding of the supplied exact
Schur roots.  Consequently two exact roots with the same count are equal.

This does not construct any root, prove a source endpoint count, identify the
ordered degree-four PSWF, or supply a Fourier/CCM rate theorem.
-/

noncomputable section

open Matrix

/-- Among exact mode-four Schur roots in the source domain, spectral-parameter
order is exactly strict order of the Hermitian negative-eigenvalue counts. -/
theorem mode4RootFunction_roots_lt_iff_negativeCount_lt
    (mProject K : ℕ) (Λ₁ Λ₂ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ₁20 : Λ₁ ≤ 20)
    (hΛ₂20 : Λ₂ ≤ 20)
    (hroot₁ : mode4RootFunction mProject K Λ₁ = 0)
    (hroot₂ : mode4RootFunction mProject K Λ₂ = 0) :
    Λ₁ < Λ₂ ↔
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ₁ K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λ₁) <
        mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ₂ K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λ₂) := by
  constructor
  · intro hlt
    have hjump :=
      mode4HermitianSchurMatrix_negativeCount_succ_le_above_root
        mProject K Λ₁ Λ₂ hm hK hsep hlt hΛ₂20 hroot₁
    omega
  · intro hcount
    by_contra hnlt
    have hle : Λ₂ ≤ Λ₁ := le_of_not_gt hnlt
    rcases hle.eq_or_lt with heq | hlt
    · subst Λ₂
      exact (lt_irrefl _ hcount)
    · have hjump :=
        mode4HermitianSchurMatrix_negativeCount_succ_le_above_root
          mProject K Λ₂ Λ₁ hm hK hsep hlt hΛ₁20 hroot₂
      omega

/-- Exact mode-four Schur roots have equal inertia labels exactly when the
roots themselves are equal.  This is the injective label needed before any
ordered-PSWF identification can be made. -/
theorem mode4RootFunction_roots_eq_iff_negativeCount_eq
    (mProject K : ℕ) (Λ₁ Λ₂ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ₁20 : Λ₁ ≤ 20)
    (hΛ₂20 : Λ₂ ≤ 20)
    (hroot₁ : mode4RootFunction mProject K Λ₁ = 0)
    (hroot₂ : mode4RootFunction mProject K Λ₂ = 0) :
    Λ₁ = Λ₂ ↔
      mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ₁ K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λ₁) =
        mode4HermitianNegativeEigenvalueCount
          (mode4HermitianSchurMatrix mProject Λ₂ K)
          (mode4HermitianSchurMatrix_isHermitian mProject K Λ₂) := by
  constructor
  · intro heq
    subst Λ₂
    rfl
  · intro hcount
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hcountLt :=
        (mode4RootFunction_roots_lt_iff_negativeCount_lt
          mProject K Λ₁ Λ₂ hm hK hsep hΛ₁20 hΛ₂20 hroot₁ hroot₂).mp hlt
      exact (ne_of_lt hcountLt) hcount
    · have hcountGt :=
        (mode4RootFunction_roots_lt_iff_negativeCount_lt
          mProject K Λ₂ Λ₁ hm hK hsep hΛ₂20 hΛ₁20 hroot₂ hroot₁).mp hgt
      exact (ne_of_gt hcountGt) hcount

#print axioms mode4RootFunction_roots_lt_iff_negativeCount_lt
#print axioms mode4RootFunction_roots_eq_iff_negativeCount_eq
