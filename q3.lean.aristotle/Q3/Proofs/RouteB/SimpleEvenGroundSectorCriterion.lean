import Mathlib

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- A nonzero eigenvector whose eigenvalue is recorded as a real number.
The exact Route B operator is self-adjoint, so this is the ordered interface
needed by the parity-sector criterion. -/
def IsRealEigenvector {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : E →ₗ[ℂ] E) (mu : ℝ) (x : E) : Prop :=
  x ≠ 0 ∧ A x = (mu : ℂ) • x

def IsEvenVector {E : Type*} [AddCommGroup E] [Module ℂ E]
    (J : E →ₗ[ℂ] E) (x : E) : Prop :=
  J x = x

def IsOddVector {E : Type*} [AddCommGroup E] [Module ℂ E]
    (J : E →ₗ[ℂ] E) (x : E) : Prop :=
  J x = -x

/-- Ordered simplicity of a real eigenvalue, without choosing a parity. -/
def IsSimpleGround {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : E →ₗ[ℂ] E) (mu0 : ℝ) (v0 : E) : Prop :=
  IsRealEigenvector A mu0 v0 ∧
    ∀ mu x, IsRealEigenvector A mu x →
      mu0 ≤ mu ∧ (mu = mu0 → ∃ c : ℂ, x = c • v0)

/-- The exact conclusion needed from the generic core: `v0` is an even
real-eigenvector at the global bottom, and every eigenvector at that level is
a scalar multiple of it. -/
def IsSimpleEvenGround {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A J : E →ₗ[ℂ] E) (mu0 : ℝ) (v0 : E) : Prop :=
  IsRealEigenvector A mu0 v0 ∧ IsEvenVector J v0 ∧
    ∀ mu x, IsRealEigenvector A mu x →
      mu0 ≤ mu ∧ (mu = mu0 → ∃ c : ℂ, x = c • v0)

/-- Algebraic even projection for a complex-linear involution. -/
def evenPart {E : Type*} [AddCommGroup E] [Module ℂ E]
    (J : E →ₗ[ℂ] E) (x : E) : E :=
  (1 / 2 : ℂ) • (x + J x)

/-- Algebraic odd projection for a complex-linear involution. -/
def oddPart {E : Type*} [AddCommGroup E] [Module ℂ E]
    (J : E →ₗ[ℂ] E) (x : E) : E :=
  (1 / 2 : ℂ) • (x - J x)

theorem evenPart_add_oddPart
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (J : E →ₗ[ℂ] E) (x : E) :
    evenPart J x + oddPart J x = x := by
  simp only [evenPart, oddPart]
  module

theorem evenPart_isEven
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (J : E →ₗ[ℂ] E) (hJ2 : ∀ x, J (J x) = x) (x : E) :
    IsEvenVector J (evenPart J x) := by
  simp only [IsEvenVector, evenPart, map_smul, map_add, hJ2]
  module

theorem oddPart_isOdd
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (J : E →ₗ[ℂ] E) (hJ2 : ∀ x, J (J x) = x) (x : E) :
    IsOddVector J (oddPart J x) := by
  simp only [IsOddVector, oddPart, map_smul, map_sub, hJ2]
  module

theorem commute_apply
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {A J : E →ₗ[ℂ] E} (hAJ : Commute A J) (x : E) :
    A (J x) = J (A x) := by
  exact LinearMap.congr_fun hAJ.eq x

theorem evenPart_isRealEigenvector_or_zero
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {A J : E →ₗ[ℂ] E} (hAJ : Commute A J)
    {mu : ℝ} {x : E} (hx : A x = (mu : ℂ) • x) :
    A (evenPart J x) = (mu : ℂ) • evenPart J x := by
  simp only [evenPart, map_smul, map_add, hx, commute_apply hAJ x]
  module

theorem oddPart_isRealEigenvector_or_zero
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {A J : E →ₗ[ℂ] E} (hAJ : Commute A J)
    {mu : ℝ} {x : E} (hx : A x = (mu : ℂ) • x) :
    A (oddPart J x) = (mu : ℂ) • oddPart J x := by
  simp only [oddPart, map_smul, map_sub, hx, commute_apply hAJ x]
  module

/-- A one-dimensional eigenspace invariant under an involution has parity
`+1` or `-1`.  Crucially, this theorem does not choose the plus sign. -/
theorem parity_dichotomy_of_simple_eigenspace
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {A J : E →ₗ[ℂ] E} {mu : ℝ} {xi : E}
    (hAJ : Commute A J) (hJ2 : ∀ x, J (J x) = x)
    (hxi : IsRealEigenvector A mu xi)
    (hsimple : ∀ y, A y = (mu : ℂ) • y → ∃ c : ℂ, y = c • xi) :
    IsEvenVector J xi ∨ IsOddVector J xi := by
  have hJxi : A (J xi) = (mu : ℂ) • J xi := by
    rw [commute_apply hAJ, hxi.2, map_smul]
  obtain ⟨c, hc⟩ := hsimple (J xi) hJxi
  have hcc : (c * c) • xi = xi := by
    calc
      (c * c) • xi = c • (c • xi) := by rw [mul_smul]
      _ = c • J xi := by rw [← hc]
      _ = J (c • xi) := by rw [map_smul]
      _ = J (J xi) := by rw [hc]
      _ = xi := hJ2 xi
  have hc2 : c ^ 2 = 1 := by
    apply smul_left_injective ℂ hxi.1
    simpa [pow_two] using hcc
  rcases sq_eq_one_iff.mp hc2 with hc_one | hc_neg
  · left
    simpa [IsEvenVector, hc_one] using hc
  · right
    simpa [IsOddVector, hc_neg] using hc

/-- Explicit sector ordering is sufficient for a simple even global ground.
The even sector supplies a lowest simple vector; every odd eigenvector is
strictly higher.  Commutation and the involution split an arbitrary
eigenvector into its even and odd parts. -/
theorem simpleEvenGround_of_sector_order
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {A J : E →ₗ[ℂ] E} {mu0 : ℝ} {v0 : E}
    (hAJ : Commute A J) (hJ2 : ∀ x, J (J x) = x)
    (hv0 : IsRealEigenvector A mu0 v0)
    (hv0even : IsEvenVector J v0)
    (hevenFloor : ∀ mu x, IsRealEigenvector A mu x →
      IsEvenVector J x → mu0 ≤ mu)
    (hevenSimple : ∀ x, IsRealEigenvector A mu0 x →
      IsEvenVector J x → ∃ c : ℂ, x = c • v0)
    (hoddStrict : ∀ mu x, IsRealEigenvector A mu x →
      IsOddVector J x → mu0 < mu) :
    IsSimpleEvenGround A J mu0 v0 := by
  refine ⟨hv0, hv0even, ?_⟩
  intro mu x hx
  let xp := evenPart J x
  let xm := oddPart J x
  have hsum : xp + xm = x := evenPart_add_oddPart J x
  have hxpeig : A xp = (mu : ℂ) • xp :=
    evenPart_isRealEigenvector_or_zero hAJ hx.2
  have hxmeig : A xm = (mu : ℂ) • xm :=
    oddPart_isRealEigenvector_or_zero hAJ hx.2
  have hxpeven : IsEvenVector J xp := evenPart_isEven J hJ2 x
  have hxmodd : IsOddVector J xm := oddPart_isOdd J hJ2 x
  by_cases hxp : xp = 0
  · have hxm : xm ≠ 0 := by
      intro hxm0
      apply hx.1
      rw [← hsum, hxp, hxm0, zero_add]
    have hstrict := hoddStrict mu xm ⟨hxm, hxmeig⟩ hxmodd
    refine ⟨hstrict.le, ?_⟩
    intro hmu
    exact (ne_of_lt hstrict hmu.symm).elim
  · have hfloor := hevenFloor mu xp ⟨hxp, hxpeig⟩ hxpeven
    refine ⟨hfloor, ?_⟩
    intro hmu
    have hxm : xm = 0 := by
      by_contra hxm0
      have hstrict := hoddStrict mu xm ⟨hxm0, hxmeig⟩ hxmodd
      exact (ne_of_lt hstrict hmu.symm)
    have hxp_eq : xp = x := by
      simpa [hxm] using hsum
    obtain ⟨c, hc⟩ := hevenSimple xp
      ⟨hxp, hmu ▸ hxpeig⟩ hxpeven
    exact ⟨c, hxp_eq ▸ hc⟩

/-- Two-dimensional parity involution `diag(1,-1)`. -/
def parityInvolution2 : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (LinearMap.id : ℂ →ₗ[ℂ] ℂ).prodMap (-LinearMap.id)

/-- Two-dimensional diagonal model `diag(1,0)`. -/
def oddGroundOperator2 : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (LinearMap.id : ℂ →ₗ[ℂ] ℂ).prodMap 0

@[simp] theorem parityInvolution2_apply (x : ℂ × ℂ) :
    parityInvolution2 x = (x.1, -x.2) := by
  rfl

@[simp] theorem oddGroundOperator2_apply (x : ℂ × ℂ) :
    oddGroundOperator2 x = (x.1, 0) := by
  rfl

theorem parityInvolution2_sq (x : ℂ × ℂ) :
    parityInvolution2 (parityInvolution2 x) = x := by
  ext <;> simp

theorem oddGroundOperator2_commutes :
    Commute oddGroundOperator2 parityInvolution2 := by
  rw [commute_iff_eq]
  apply LinearMap.ext
  intro x
  ext <;> simp [Module.End.mul_apply]

theorem oddGroundVector2_is_simple_zero_eigenvector :
    IsRealEigenvector oddGroundOperator2 0 (0, 1) ∧
      (∀ y, oddGroundOperator2 y = (0 : ℂ) • y →
        ∃ c : ℂ, y = c • (0, 1)) := by
  constructor
  · constructor
    · norm_num
    · simp
  · intro y hy
    have hy1 : y.1 = 0 := by
      simpa [Prod.ext_iff] using congr_arg Prod.fst hy
    refine ⟨y.2, ?_⟩
    ext <;> simp [hy1]

theorem oddGroundVector2_is_odd :
    IsOddVector parityInvolution2 (0, 1) := by
  simp [IsOddVector]

theorem oddGroundVector2_is_simple_ground :
    IsSimpleGround oddGroundOperator2 0 (0, 1) := by
  refine ⟨oddGroundVector2_is_simple_zero_eigenvector.1, ?_⟩
  intro mu x hx
  have hfirst : x.1 = (mu : ℂ) * x.1 := by
    simpa using congr_arg Prod.fst hx.2
  have hsecond : 0 = (mu : ℂ) * x.2 := by
    simpa using congr_arg Prod.snd hx.2
  by_cases hx2 : x.2 = 0
  · have hx1 : x.1 ≠ 0 := by
      intro hx1
      apply hx.1
      exact Prod.ext hx1 hx2
    have hmuC : (mu : ℂ) = 1 := by
      apply mul_right_cancel₀ hx1
      simpa using hfirst.symm
    have hmu : mu = 1 := by
      exact_mod_cast hmuC
    constructor
    · rw [hmu]
      norm_num
    · intro hzero
      norm_num [hmu] at hzero
  · have hmuC : (mu : ℂ) = 0 := by
      rcases mul_eq_zero.mp hsecond.symm with hmu | hx2zero
      · exact hmu
      · exact (hx2 hx2zero).elim
    have hmu : mu = 0 := by
      exact_mod_cast hmuC
    constructor
    · rw [hmu]
    · intro _
      have hx1 : x.1 = 0 := by
        simpa [hmu] using hfirst
      refine ⟨x.2, ?_⟩
      ext <;> simp [hx1]

/-- Executable falsifier: commuting involution plus a simple ground
eigenspace does not imply that the ground vector is even. -/
theorem commute_simple_ground_does_not_force_even :
    Commute oddGroundOperator2 parityInvolution2 ∧
      (∀ x, parityInvolution2 (parityInvolution2 x) = x) ∧
      IsSimpleGround oddGroundOperator2 0 (0, 1) ∧
      IsOddVector parityInvolution2 (0, 1) := by
  exact ⟨oddGroundOperator2_commutes, parityInvolution2_sq,
    oddGroundVector2_is_simple_ground,
    oddGroundVector2_is_odd⟩

#print axioms parity_dichotomy_of_simple_eigenspace
#print axioms simpleEvenGround_of_sector_order
#print axioms commute_simple_ground_does_not_force_even

end Q3.RouteB
