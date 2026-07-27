import Mathlib

open Matrix
open scoped ComplexOrder

/-!
# H2a — Simple even ground state from penalty coercivity

This file proves a **basis-invariant finite-dimensional** theorem underlying slot `H2a`
of the RH route.  It concerns the generalized (Hermitian pencil) eigenproblem
`K x = λ (G x)` with `G` positive definite.

Given a self-adjoint `K`, a positive-definite `G`, an involution `J` commuting with the
pencil, a `J`-even, `G`-normalized vector `q` with Rayleigh value `a := q* K q`, and a
**penalty/coercivity certificate**
`K - β G + τ (Gq)(Gq)* ⪰ 0`  with `a < β`,
we prove:

* the pencil has a **lowest generalized eigenvalue** `λ₁ ≤ a`, and `λ₁` is the minimum
  of the whole spectrum;
* the lowest eigenvalue is **simple** (its generalized eigenspace is one-dimensional);
* there is a **spectral gap** `λ₂ - λ₁ ≥ β - a > 0` (every other eigenvalue is `≥ β`),
  hence `λ₁` is isolated;
* **every** lowest eigenvector is `J`-even.

The proof route is: whiten by `G^{1/2}` for existence of the lowest eigenpair (isolated
in `exists_lowest`), then derive `β`-coercivity on the `G`-orthogonal complement of `q`
from the certificate, and finish with elementary pencil linear algebra plus the
`J`-invariance/`G`-orthogonality of odd vectors.
-/

namespace H2aPenalty

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A **generalized eigenpair** of the Hermitian pencil `(K, G)`: a nonzero `x` with
`K x = μ (G x)` and real eigenvalue `μ`. -/
def GEig (K G : Matrix n n ℂ) (μ : ℝ) (x : n → ℂ) : Prop :=
  x ≠ 0 ∧ K *ᵥ x = (μ : ℂ) • (G *ᵥ x)

/-! ## Elementary quadratic-form facts. -/

/-
The quadratic form of a Hermitian matrix is real.
-/
theorem qf_isHermitian_im (A : Matrix n n ℂ) (hA : A.IsHermitian) (x : n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 := by
  have h_real : star x ⬝ᵥ A *ᵥ x = star (star x ⬝ᵥ A *ᵥ x) := by
    simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum ];
    rw [ Finset.sum_comm ] ; congr ; ext i ; congr ; ext j ; rw [ ← hA.apply ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  exact Complex.conj_eq_iff_im.mp h_real.symm

/-
Reading off the Rayleigh quotient from an eigenpair: `x* K x = μ (x* G x)`.
-/
theorem geig_quad {K G : Matrix n n ℂ} {μ : ℝ} {x : n → ℂ}
    (h : GEig K G μ x) :
    star x ⬝ᵥ (K *ᵥ x) = (μ : ℂ) * (star x ⬝ᵥ (G *ᵥ x)) := by
  convert congr_arg ( fun y => star x ⬝ᵥ y ) h.2 using 1 ; simp +decide [ Matrix.mulVec_smul ]

/-
Eigenvectors of the pencil for distinct eigenvalues are `G`-orthogonal.
-/
theorem geig_Gorth_of_ne {K G : Matrix n n ℂ} (hK : K.IsHermitian) (hG : G.IsHermitian)
    {μ ν : ℝ} {x y : n → ℂ}
    (hx : GEig K G μ x) (hy : GEig K G ν y) (hμν : μ ≠ ν) :
    star x ⬝ᵥ (G *ᵥ y) = 0 := by
  -- Use the fact that $K$ is Hermitian to rewrite the inner product.
  have h_inner : star x ⬝ᵥ (K *ᵥ y) = star (K *ᵥ x) ⬝ᵥ y := by
    simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_comm ];
    rw [ Finset.sum_comm ] ; congr ; ext ; congr ; ext ; rw [ ← hK.apply ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  have h_inner : star x ⬝ᵥ (K *ᵥ y) = (ν : ℂ) * (star x ⬝ᵥ (G *ᵥ y)) := by
    simp +decide [ hy.2, Matrix.mulVec_smul ]
  have h_inner' : star (K *ᵥ x) ⬝ᵥ y = (μ : ℂ) * (star (G *ᵥ x) ⬝ᵥ y) := by
    convert congr_arg ( fun z => star z ⬝ᵥ y ) hx.2 using 1 ; simp +decide [ Matrix.mulVec_smul ]
  have h_inner_eq : (ν : ℂ) * (star x ⬝ᵥ (G *ᵥ y)) = (μ : ℂ) * (star x ⬝ᵥ (G *ᵥ y)) := by
    have h_inner_eq : star (G *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (G *ᵥ y) := by
      simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, hG.eq ];
      rw [ Finset.sum_comm ] ; congr ; ext i ; congr ; ext j ; rw [ ← hG.apply ] ; ring;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
    grobner
  have h_inner_zero : (star x ⬝ᵥ (G *ᵥ y)) = 0 := by
    exact Classical.not_not.1 fun h => hμν <| by simpa [ h ] using h_inner_eq.symm;
  exact h_inner_zero

/-
**β-coercivity on `q^{⊥_G}`.**  From the penalty certificate, any vector `x`
that is `G`-orthogonal to `q` satisfies `β (x* G x) ≤ x* K x`.
-/
theorem coercivity {G K : Matrix n n ℂ} {q : n → ℂ} {β τ : ℝ} (hG : G.IsHermitian)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef)
    {x : n → ℂ} (hx : star q ⬝ᵥ (G *ᵥ x) = 0) :
    (β : ℂ) * (star x ⬝ᵥ (G *ᵥ x)) ≤ star x ⬝ᵥ (K *ᵥ x) := by
  have := hcert.2;
  have h_pos : star x ⬝ᵥ ((K - β • G + τ • (vecMulVec (G *ᵥ q) (star (G *ᵥ q)))) *ᵥ x) = star x ⬝ᵥ (K *ᵥ x) - β * star x ⬝ᵥ (G *ᵥ x) := by
    have h_pos : star x ⬝ᵥ (vecMulVec (G *ᵥ q) (star (G *ᵥ q)) *ᵥ x) = (star (G *ᵥ q) ⬝ᵥ x) * (star x ⬝ᵥ (G *ᵥ q)) := by
      simp +decide [ Matrix.vecMulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      simp +decide [ Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    have h_pos : star (G *ᵥ q) ⬝ᵥ x = star q ⬝ᵥ G *ᵥ x := by
      simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
      rw [ Finset.sum_comm ];
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [ ← Matrix.IsHermitian.apply hG ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    simp_all +decide [ Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_eq_diagonal_mul ];
    simp_all +decide [ Matrix.mulVec, dotProduct ];
    simp_all +decide [ mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  convert sub_nonneg.mp ( show 0 ≤ star x ⬝ᵥ ( K *ᵥ x ) - ↑β * ( star x ⬝ᵥ G *ᵥ x ) from ?_ ) using 1;
  convert this ( Finsupp.equivFunOnFinite.symm x ) using 1;
  convert h_pos.symm using 1;
  simp +decide [ Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ]

/-
Two directions can always be combined into a nonzero coefficient pair that lands
in `q^{⊥_G}` (one homogeneous linear equation in two unknowns).
-/
theorem exists_combo_Gorth (G : Matrix n n ℂ) (q x y : n → ℂ) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧
      s * (star q ⬝ᵥ (G *ᵥ x)) + t * (star q ⬝ᵥ (G *ᵥ y)) = 0 := by
  by_cases hb : star q ⬝ᵥ G *ᵥ y = 0;
  · exact ⟨ 0, 1, by simp +decide, by simp +decide [ hb ] ⟩;
  · refine' ⟨ -star q ⬝ᵥ G *ᵥ y, star q ⬝ᵥ G *ᵥ x, _, _ ⟩ <;> simp_all +decide [ mul_comm ]

/-! ## `J`-symmetry facts. -/

/-
The involution `J` maps generalized eigenvectors to generalized eigenvectors with the
same eigenvalue.
-/
theorem J_geig {K G J : Matrix n n ℂ} {μ : ℝ} {x : n → ℂ}
    (hJ : J * J = 1) (hJG : Jᴴ * G * J = G) (hJK : Jᴴ * K * J = K)
    (h : GEig K G μ x) :
    GEig K G μ (J *ᵥ x) := by
  refine' ⟨ _, _ ⟩;
  · intro h';
    apply_fun fun y => J *ᵥ y at h' ; simp_all +decide [ Matrix.mulVec_mulVec ];
    exact h.1 rfl;
  · have hOp : K * J = Jᴴ * K ∧ G * J = Jᴴ * G := by
      apply_fun ( fun m => m * J ) at hJK hJG; simp_all +decide [ mul_assoc ] ;
    simp_all +decide [ ← Matrix.mul_assoc, GEig ];
    simp_all +decide [ ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul ]

/-
A `J`-odd vector is `G`-orthogonal to the `J`-even vector `q`.
-/
theorem odd_Gorth {G J : Matrix n n ℂ} {q x : n → ℂ}
    (hJG : Jᴴ * G * J = G) (hJq : J *ᵥ q = q) (hodd : J *ᵥ x = -x) :
    star q ⬝ᵥ (G *ᵥ x) = 0 := by
  -- From `hJG : Jᴴ * G * J = G`, rewrite `G *ᵥ x = (Jᴴ * G * J) *ᵥ x`. Using `Matrix.mulVec_mulVec` (`(A*B) *ᵥ v = A *ᵥ (B *ᵥ v)`), this is `Jᴴ *ᵥ (G *ᵥ (J *ᵥ x))`. By `hodd : J *ᵥ x = -x`, `G *ᵥ (J *ᵥ x) = G *ᵥ (-x) = -(G *ᵥ x)`. So `G *ᵥ x = - (Jᴴ *ᵥ (G *ᵥ x))`.
  have hGx : G *ᵥ x = - (star J *ᵥ (G *ᵥ x)) := by
    convert congr_arg ( fun m => m *ᵥ x ) hJG.symm using 1;
    simp +decide [ ← Matrix.mulVec_mulVec, hodd ];
    simp +decide [ Matrix.mulVec, funext_iff ];
    exact fun x_2 => Complex.ext rfl rfl;
  -- By `hodd : J *ᵥ x = -x`, we have `star q ⬝ᵥ (Jᴴ *ᵥ (G *ᵥ x)) = star (J *ᵥ q) ⬝ᵥ (G *ᵥ x)`.
  have hstarJq : star q ⬝ᵥ (star J *ᵥ (G *ᵥ x)) = star (J *ᵥ q) ⬝ᵥ (G *ᵥ x) := by
    simp +decide [ Matrix.mulVec, dotProduct ];
    simp +decide only [mul_comm, Finset.mul_sum _ _ _];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  replace hGx := congr_arg ( fun z => star q ⬝ᵥ z ) hGx; norm_num at *;
  grind

/-! ## Existence of the lowest eigenpair (whitening + spectral theorem). -/

/-
**Variational lowest eigenvalue of a Hermitian matrix.**  A Hermitian matrix `M`
on a nonempty index has a lowest eigenvalue `lam` with eigenvector `v ≠ 0`, and
`lam` is a Rayleigh lower bound: `lam (w* w) ≤ w* M w` for all `w`.
-/
theorem hermitian_min_eig [Nonempty n] {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∃ (lam : ℝ) (v : n → ℂ), v ≠ 0 ∧ M *ᵥ v = (lam : ℂ) • v ∧
      ∀ w : n → ℂ, lam * (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ (M *ᵥ w)).re := by
  -- Let $\mu$ be the smallest eigenvalue of $M$.
  obtain ⟨μ, hμ⟩ : ∃ μ ∈ Set.range (fun j => hM.eigenvalues j), ∀ ν ∈ Set.range (fun j => hM.eigenvalues j), μ ≤ ν := by
    exact ⟨ Finset.min' ( Set.toFinset ( Set.range fun j => hM.eigenvalues j ) ) ⟨ _, Set.mem_toFinset.mpr ( Set.mem_range_self ( Classical.arbitrary n ) ) ⟩, Set.mem_toFinset.mp ( Finset.min'_mem _ _ ), fun ν hν => Finset.min'_le _ _ ( Set.mem_toFinset.mpr hν ) ⟩;
  obtain ⟨ j, rfl ⟩ := hμ.1;
  refine' ⟨ hM.eigenvalues j, hM.eigenvectorBasis j, _, hM.mulVec_eigenvectorBasis j, _ ⟩;
  · exact ne_of_apply_ne ( fun x => ‖x‖ ) ( by simp +decide [ hM.eigenvectorBasis.orthonormal.ne_zero ] );
  · intro w
    set y := (hM.eigenvectorUnitary : Matrix n n ℂ).conjTranspose.mulVec w
    have h_y_norm : (star w ⬝ᵥ w).re = ∑ i, ‖y i‖^2 := by
      have h_y_norm : (star w ⬝ᵥ w) = (star y ⬝ᵥ y) := by
        simp +zetaDelta at *;
        simp +decide [ Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.star_mulVec ];
        simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
      simp_all +decide [ Complex.normSq, Complex.sq_norm, dotProduct ]
    have h_y_Mw : (star w ⬝ᵥ (M *ᵥ w)).re = ∑ i, hM.eigenvalues i * ‖y i‖^2 := by
      have h_y_Mw : (star w ⬝ᵥ (M *ᵥ w)) = ∑ i, hM.eigenvalues i * (star (y i) * y i) := by
        have h_y_Mw : (star w ⬝ᵥ (M *ᵥ w)) = (star y ⬝ᵥ (Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) *ᵥ y)) := by
          have h_y_Mw : M = (hM.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) * (hM.eigenvectorUnitary : Matrix n n ℂ).conjTranspose := by
            convert hM.spectral_theorem using 1;
          simp +zetaDelta at *;
          conv_lhs => rw [ h_y_Mw ];
          simp +decide [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.star_mulVec ];
        simp_all +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
        simp +decide [ Matrix.diagonal, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      simp_all +decide [ Complex.normSq, Complex.sq_norm ];
    rw [ h_y_norm, h_y_Mw, Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( hμ.2 _ ( Set.mem_range_self i ) ) ( sq_nonneg _ )

/-
**Lowest generalized eigenpair.**  For the pencil `(K, G)` with `G` positive definite,
there is a lowest eigenvalue `lam` with eigenvector `x ≠ 0`, and `lam` is a generalized
Rayleigh lower bound: `lam (z* G z) ≤ z* K z` for all `z`.  (Proved by whitening
`M := G^{-1/2} K G^{-1/2}` and applying `hermitian_min_eig`.)
-/
theorem exists_lowest [Nonempty n] {G K : Matrix n n ℂ}
    (hG : G.PosDef) (hK : K.IsHermitian) :
    ∃ (lam : ℝ) (x : n → ℂ), x ≠ 0 ∧ K *ᵥ x = (lam : ℂ) • (G *ᵥ x) ∧
      ∀ z : n → ℂ, lam * (star z ⬝ᵥ (G *ᵥ z)).re ≤ (star z ⬝ᵥ (K *ᵥ z)).re := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n ℂ, S.IsHermitian ∧ S * S = G ∧ S.PosDef := by
    convert hG.posDef_sqrt using 1;
    constructor <;> intro h;
    · convert hG.posDef_sqrt;
    · refine' ⟨ _, _, _, h ⟩;
      · convert h.1 using 1;
      · convert hG.posSemidef.sqrt_mul_self;
  obtain ⟨lam, v, hv_ne_zero, hv_eigen, hv_var⟩ : ∃ lam : ℝ, ∃ v : n → ℂ, v ≠ 0 ∧ (S⁻¹ * K * S⁻¹) *ᵥ v = lam • v ∧ ∀ w : n → ℂ, lam * (star w ⬝ᵥ w).re ≤ (star w ⬝ᵥ ((S⁻¹ * K * S⁻¹) *ᵥ w)).re := by
    apply hermitian_min_eig;
    simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
    rw [ Matrix.conjTranspose_nonsing_inv, hS.1 ];
  refine' ⟨ lam, S⁻¹ *ᵥ v, _, _, _ ⟩;
  · intro h; have := hS.2.2.det_pos; simp_all +decide [ Matrix.nonsing_inv_apply_not_isUnit, isUnit_iff_ne_zero ] ;
    apply_fun S.mulVec at h; simp_all +decide [ isUnit_iff_ne_zero, ne_of_gt ] ;
  · convert congr_arg ( fun x => S *ᵥ x ) hv_eigen using 1;
    · simp +decide [ Matrix.mul_assoc, hS.2.2.det_pos.ne' ];
    · simp +decide [ ← hS.2.1, Matrix.mulVec_smul ];
      rw [ Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ];
      · simp +decide [ Matrix.mulVec, funext_iff ];
      · exact isUnit_iff_ne_zero.mpr hS.2.2.det_pos.ne';
  · intro z
    specialize hv_var (S *ᵥ z);
    convert hv_var using 1;
    · simp +decide [ ← hS.2.1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hS.1.eq ];
      simp +decide [ Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hS.1.eq ];
    · simp +decide [ Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hS.1.eq, hS.2.1, hS.2.2.det_pos.ne' ]

/-! ## The three conclusion clauses. -/

/-
**Simplicity.**  If `lam < β`, the generalized eigenspace for `lam` is
one-dimensional: any two `lam`-eigenvectors are proportional.
-/
theorem simplicity_clause {G K : Matrix n n ℂ} {q : n → ℂ} {β τ lam : ℝ}
    (hG : G.PosDef)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef)
    (hlamβ : lam < β) :
    ∀ x y, GEig K G lam x → GEig K G lam y → ∃ c : ℂ, y = c • x := by
  intro x y hx hy
  obtain ⟨s, t, hst, hcombo⟩ := exists_combo_Gorth G q x y
  set z := s • x + t • y with hz_def
  have hz_eigen : K *ᵥ z = (lam:ℂ) • (G *ᵥ z) := by
    simp_all +decide [ mul_add, add_mul, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.mulVec_add, Matrix.mulVec_smul ];
    rw [ hx.2, hy.2 ] ; ext ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  have hz_orthogonal : star q ⬝ᵥ (G *ᵥ z) = 0 := by
    simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul ]
  have hz_zero : z = 0 := by
    have hz_zero : (β : ℂ) * (star z ⬝ᵥ (G *ᵥ z)) ≤ star z ⬝ᵥ (K *ᵥ z) := by
      apply coercivity hG.1 hcert hz_orthogonal;
    by_cases hz_nonzero : z ≠ 0;
    · have hz_pos : 0 < (star z ⬝ᵥ (G *ᵥ z)).re := by
        apply hG.dotProduct_mulVec_pos hz_nonzero |>.1;
      simp_all +decide [ Complex.le_def ];
      nlinarith;
    · exact Classical.not_not.mp hz_nonzero
  have ht_nonzero : t ≠ 0 := by
    contrapose! hst; simp_all +decide [ funext_iff ] ;
    exact Classical.not_not.1 fun hs => hx.1 <| funext fun i => Or.resolve_left ( hz_def i ) hs
  use (-(s * (t⁻¹)));
  simp_all +decide [ ← eq_sub_iff_add_eq', funext_iff, smul_smul ];
  grind

/-
**Spectral gap.**  Given a `lam`-eigenvector `x₁` with `lam < β`, every eigenvalue
`μ ≠ lam` satisfies `β ≤ μ`.
-/
set_option maxHeartbeats 1600000 in
theorem gap_clause {G K : Matrix n n ℂ} {q : n → ℂ} {β τ lam : ℝ}
    (hG : G.PosDef) (hK : K.IsHermitian)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef)
    (hlamβ : lam < β) {x₁ : n → ℂ} (hx₁ : GEig K G lam x₁) :
    ∀ μ y, GEig K G μ y → μ ≠ lam → β ≤ μ := by
  intro μ y hy hμ_ne_lam
  obtain ⟨s, t, hst, hcombo⟩ := exists_combo_Gorth G q x₁ y
  obtain ⟨hx₁_ne_zero, hx₁_eq⟩ := hx₁
  obtain ⟨hy_ne_zero, hy_eq⟩ := hy
  have hxy : star x₁ ⬝ᵥ (G *ᵥ y) = 0 := by
    apply geig_Gorth_of_ne hK hG.1 ⟨hx₁_ne_zero, hx₁_eq⟩ ⟨hy_ne_zero, hy_eq⟩ (Ne.symm hμ_ne_lam)
  have hyx : star y ⬝ᵥ (G *ᵥ x₁) = 0 := by
    convert geig_Gorth_of_ne hK hG.1 ⟨ hy_ne_zero, hy_eq ⟩ ⟨ hx₁_ne_zero, hx₁_eq ⟩ hμ_ne_lam using 1
  have hx1_gt_zero : 0 < (star x₁ ⬝ᵥ (G *ᵥ x₁)).re := by
    convert hG.dotProduct_mulVec_pos hx₁_ne_zero using 1;
    simp +decide [ Complex.lt_def ];
    exact fun _ => qf_isHermitian_im _ hG.1 _ ▸ rfl
  have hy_gt_zero : 0 < (star y ⬝ᵥ (G *ᵥ y)).re := by
    convert hG.dotProduct_mulVec_pos hy_ne_zero using 1;
    rw [ Complex.lt_def ] ; norm_num;
    have := hG.1;
    exact fun _ => Eq.symm ( qf_isHermitian_im G this y )
  by_cases hβ_gt_μ : β > μ;
  · -- Let $z := s • x₁ + t • y$. Then $z ≠ 0$ and $star q ⬝ᵥ (G *ᵥ z) = 0$.
    set z : n → ℂ := s • x₁ + t • y
    have hz_ne_zero : z ≠ 0 := by
      have hz_ne_zero : star x₁ ⬝ᵥ (G *ᵥ z) = s * (star x₁ ⬝ᵥ (G *ᵥ x₁)) + t * (star x₁ ⬝ᵥ (G *ᵥ y)) := by
        simp +decide [ z, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul ];
      aesop
    have hqz : star q ⬝ᵥ (G *ᵥ z) = 0 := by
      convert hcombo using 1;
      simp +decide [ z, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul ];
    -- Now apply `coercivity hG.isHermitian hcert hqz : (β:ℂ) * (star z ⬝ᵥ G*ᵥz) ≤ star z ⬝ᵥ K*ᵥz` and take real parts with `Complex.le_def`.
    have hcoercivity : (β : ℂ) * (star z ⬝ᵥ (G *ᵥ z)) ≤ star z ⬝ᵥ (K *ᵥ z) := by
      convert coercivity hG.1 hcert hqz using 1;
    -- Expand `star z ⬝ᵥ (G *ᵥ z)` and `star z ⬝ᵥ (K *ᵥ z)` using bilinearity and the two orthogonalities `hxy, hyx`.
    have hGzz : star z ⬝ᵥ (G *ᵥ z) = (starRingEnd ℂ s * s) * (star x₁ ⬝ᵥ (G *ᵥ x₁)) + (starRingEnd ℂ t * t) * (star y ⬝ᵥ (G *ᵥ y)) := by
      simp +zetaDelta at *;
      simp +decide [ Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, mul_assoc, hxy, hyx ]
    have hKzz : star z ⬝ᵥ (K *ᵥ z) = (starRingEnd ℂ s * s) * ((lam : ℂ) * (star x₁ ⬝ᵥ (G *ᵥ x₁))) + (starRingEnd ℂ t * t) * ((μ : ℂ) * (star y ⬝ᵥ (G *ᵥ y))) := by
      simp +zetaDelta at *;
      simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct ];
      ring;
    simp_all +decide [ Complex.le_def ];
    -- Since $s \neq 0$ or $t \neq 0$, we have $(s.re * s.re + s.im * s.im) > 0$ or $(t.re * t.re + t.im * t.im) > 0$.
    have h_pos : (s.re * s.re + s.im * s.im) > 0 ∨ (t.re * t.re + t.im * t.im) > 0 := by
      contrapose! hst; simp_all +decide [ Complex.ext_iff ] ;
      exact ⟨ ⟨ by nlinarith only [ hst.1 ], by nlinarith only [ hst.1 ] ⟩, ⟨ by nlinarith only [ hst.2 ], by nlinarith only [ hst.2 ] ⟩ ⟩;
    cases' h_pos with h_pos h_pos <;> nlinarith [ mul_pos h_pos hx1_gt_zero, mul_pos h_pos hy_gt_zero, mul_lt_mul_of_pos_left hlamβ hx1_gt_zero, mul_lt_mul_of_pos_left hβ_gt_μ hy_gt_zero ];
  · linarith

/-
**Evenness.**  If the `lam`-eigenspace is simple and `lam < β`, every
`lam`-eigenvector is `J`-even.
-/
theorem even_clause {G K J : Matrix n n ℂ} {q : n → ℂ} {β τ lam : ℝ}
    (hG : G.PosDef)
    (hJ : J * J = 1) (hJG : Jᴴ * G * J = G) (hJK : Jᴴ * K * J = K) (hJq : J *ᵥ q = q)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef)
    (hlamβ : lam < β)
    (hsimple : ∀ x y, GEig K G lam x → GEig K G lam y → ∃ c : ℂ, y = c • x) :
    ∀ x, GEig K G lam x → J *ᵥ x = x := by
  intro x hx
  have hJx : GEig K G lam (J *ᵥ x) := by
    convert J_geig hJ hJG hJK hx using 1
  obtain ⟨c, hc⟩ := hsimple x (J *ᵥ x) hx hJx
  have hc_sq : c^2 = 1 := by
    have hc_sq : J *ᵥ (J *ᵥ x) = x := by
      simp +decide [ ← Matrix.mul_assoc, hJ ];
    simp_all +decide [ sq, Matrix.mulVec_smul ];
    obtain ⟨ i, hi ⟩ := Function.ne_iff.mp hx.1; replace hc_sq := congr_fun hc_sq i; simp_all +decide [ mul_assoc, smul_smul ] ;
    exact mul_left_cancel₀ hi <| by linear_combination' hc_sq;
  have hc_cases : c = 1 ∨ c = -1 := by
    exact sq_eq_one_iff.mp hc_sq
  cases' hc_cases with hc1 hc_neg1;
  · aesop;
  · have h_odd_Gorth : star q ⬝ᵥ (G *ᵥ x) = 0 := by
      apply odd_Gorth hJG hJq; simp [hc_neg1, hc];
    have h_coercivity : β * (star x ⬝ᵥ (G *ᵥ x)).re ≤ (star x ⬝ᵥ (K *ᵥ x)).re := by
      have := coercivity hG.1 hcert h_odd_Gorth;
      convert Complex.le_def.mp this |>.1 using 1;
      simp +decide [ dotProduct, Complex.ext_iff ];
    have h_rayleigh : star x ⬝ᵥ (K *ᵥ x) = lam * (star x ⬝ᵥ (G *ᵥ x)) := by
      convert geig_quad hx using 1;
    have h_pos : 0 < (star x ⬝ᵥ (G *ᵥ x)).re := by
      convert hG.dotProduct_mulVec_pos hx.1 using 1;
      have := qf_isHermitian_im G hG.1 x; simp_all +decide [ Complex.ext_iff ] ;
      rw [ ← Complex.re_add_im ( star x ⬝ᵥ G *ᵥ x ) ] ; aesop;
    norm_num [ h_rayleigh ] at h_coercivity; nlinarith;

/-! ## Main theorem. -/

/-
**H2a: simple, isolated, `J`-even ground state from penalty coercivity.**

Given `G = G* > 0`, `K = K*`, an involution `J` with `J* G J = G`, `J* K J = K`, a
`J`-even `G`-unit vector `q` (`J q = q`, `q* G q = 1`) with Rayleigh value `a = q* K q`,
`a < β`, and the penalty certificate `K - β G + τ (Gq)(Gq)* ⪰ 0`, the generalized
eigenproblem `K x = λ (G x)` has:

* a lowest eigenvalue `λ₁ ≤ a`, which is the minimum of the spectrum;
* a spectral gap: every eigenvalue `μ ≠ λ₁` satisfies `β - a ≤ μ - λ₁` (so `λ₂ - λ₁ ≥ β - a`
  and `λ₁` is isolated);
* simplicity: the `λ₁`-eigenspace is one-dimensional;
* evenness: every `λ₁`-eigenvector is `J`-even.
-/
theorem H2a_SimpleEvenGround_FromPenaltyCoercivity
    (G K J : Matrix n n ℂ) (q : n → ℂ) (a β τ : ℝ)
    (hG : G.PosDef) (hK : K.IsHermitian)
    (hJ : J * J = 1) (hJG : Jᴴ * G * J = G) (hJK : Jᴴ * K * J = K)
    (hJq : J *ᵥ q = q)
    (hq : star q ⬝ᵥ (G *ᵥ q) = 1)
    (ha : star q ⬝ᵥ (K *ᵥ q) = (a : ℂ))
    (hab : a < β)
    (hcert : (K - (β : ℂ) • G + (τ : ℂ) • Matrix.vecMulVec (G *ᵥ q) (star (G *ᵥ q))).PosSemidef) :
    ∃ lam : ℝ,
      (∃ x, GEig K G lam x) ∧
      lam ≤ a ∧
      (∀ μ y, GEig K G μ y → lam ≤ μ) ∧
      (∀ μ y, GEig K G μ y → μ ≠ lam → β - a ≤ μ - lam) ∧
      (∀ x y, GEig K G lam x → GEig K G lam y → ∃ c : ℂ, y = c • x) ∧
      (∀ x, GEig K G lam x → J *ᵥ x = x) := by
  obtain ⟨lam, x, hx⟩ : ∃ lam : ℝ, ∃ x : n → ℂ, GEig K G lam x ∧ lam ≤ a := by
    have h_nonempty : Nonempty n := by
      contrapose! hq; aesop;
    have := exists_lowest hG hK;
    obtain ⟨ lam, x, hx₁, hx₂, hx₃ ⟩ := this; use lam, x; simp_all +decide [ GEig ] ;
    specialize hx₃ q; simp_all +decide [ Complex.ext_iff ] ;
  use lam;
  refine' ⟨ ⟨ x, hx.1 ⟩, hx.2, _, _, _, _ ⟩;
  · intro μ y hy;
    by_cases hμlam : μ = lam;
    · rw [ hμlam ];
    · apply gap_clause hG hK hcert (by linarith) hx.left μ y hy hμlam |> le_trans (by linarith);
  · intro μ y hy hne; have := gap_clause hG hK hcert ( by linarith ) hx.1 μ y hy hne; linarith;
  · apply simplicity_clause hG hcert (by linarith);
  · apply even_clause hG hJ hJG hJK hJq hcert (by linarith) (simplicity_clause hG hcert (by linarith))

/-!
## Next step: family instantiation

The abstract theorem `H2a_SimpleEvenGround_FromPenaltyCoercivity` above is the finite,
basis-invariant engine of slot `H2a`.  The next lemma to prove is the **family
instantiation** feeding it into the RH route (`RequestProject/Main.lean`):

theorem `SIEG_of_penalty` : given `RHRoute.Approx P` and index `j`, the concrete finite
data `(n, G, K, J, q, a, β, τ)` attached to the `j`-th approximant `F_j` satisfying the
eight hypotheses of `H2a_SimpleEvenGround_FromPenaltyCoercivity` (in particular the
penalty certificate `K - β G + τ (Gq)(Gq)* ⪰ 0` with `a < β`), together with a bridge
relating this `(K, G)`-pencil eigenproblem to the transform used by the abstract predicate
`RHRoute.SIEG`, yields `RHRoute.SIEG P j`.  Its proof applies
`H2a_SimpleEvenGround_FromPenaltyCoercivity` to obtain the simple, isolated, `J`-even
lowest generalized eigenvalue, then transports that conclusion across the bridge.  That
lemma, plus the actual construction of `(G_j, K_j, J_j, q_j)` and a verified certificate
for each `j`, is what discharges `RHRoute.supply_H2a`.
-/

end H2aPenalty