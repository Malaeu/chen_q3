/-
Minimal RKHS-style interface for the nontrivial C1 `hA`
=======================================================

This file isolates the *exact* hypotheses needed to justify the paper's “C1 bridge”:

  `T_P^{Ray}(t,M) = ι† · T_P^{RKHS}(t) · ι`

without committing to a full RKHS development in Lean.

We model the RKHS side by:
- a Hilbert space `H`,
- an orthonormal family `ψ : Fin (2M+1) → H` (the “features”),
- vectors `k n : H` indexed by `Nodes K` (the “kernel sections”),
  with the matching hypothesis `⟪ψ i, k n⟫ = prime_vec ... i`.

From this data we build:
- a linear isometry `ι : EuclideanSpace ℂ (Fin (2M+1)) →ₗᵢ[ℂ] H` sending standard basis vectors
  to `ψ`,
- an “RKHS-like prime operator” `T` as a finite sum of rank-one operators `k n ⊗ k n`,
and prove that `T_P_comp` is exactly the compression of `T` by `ι`.
-/

import Q3.Basic.Defs
import Q3.Proofs.C1_Embedding
import Mathlib.Analysis.InnerProductSpace.Orthonormal

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open scoped ComplexConjugate

namespace Q3.Proofs
namespace RKHSInterfaceC1

open Module
open Q3
open Q3.Proofs.C1Embedding

variable (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "mDim" => Fin (2 * M + 1)
local notation "E" => EuclideanSpace ℂ mDim

/-- Linear map `E → H` induced by `ψ : mDim → H`: `x ↦ ∑ xᵢ • ψᵢ`. -/
noncomputable def iotaLin (ψ : mDim → H) : E →ₗ[ℂ] H where
  toFun x := ∑ i : mDim, x i • ψ i
  map_add' x y := by
    classical
    simp [Finset.sum_add_distrib, add_smul]
  map_smul' c x := by
    classical
    simp [Finset.smul_sum, smul_smul]

lemma iotaLin_apply_basisFun (ψ : mDim → H) (i : mDim) :
    iotaLin (M := M) ψ (EuclideanSpace.basisFun mDim ℂ i) = ψ i := by
  classical
  simp [iotaLin, EuclideanSpace.basisFun_apply]

/-- Linear isometry `ι : E →ₗᵢ[ℂ] H` sending the standard orthonormal basis to `ψ`. -/
noncomputable def iota (ψ : mDim → H) (hψ : Orthonormal ℂ ψ) : E →ₗᵢ[ℂ] H := by
  classical
  let v : Basis mDim ℂ E := (EuclideanSpace.basisFun mDim ℂ).toBasis
  have hv : Orthonormal ℂ v := by
    simpa [v] using (EuclideanSpace.basisFun mDim ℂ).orthonormal
  have hf : Orthonormal ℂ ((iotaLin (M := M) ψ) ∘ v) := by
    have hcomp : ((iotaLin (M := M) ψ) ∘ v) = ψ := by
      funext i
      simpa [Function.comp, v] using iotaLin_apply_basisFun (M := M) (ψ := ψ) i
    -- Rewrite the goal by the identified family.
    simpa [hcomp] using hψ
  exact (iotaLin (M := M) ψ).isometryOfOrthonormal hv hf

lemma iota_toLinearMap (ψ : mDim → H) (hψ : Orthonormal ℂ ψ) :
    (iota (M := M) (ψ := ψ) hψ).toLinearMap = iotaLin (M := M) ψ := by
  classical
  simp [iota]

lemma iota_apply_basisFun (ψ : mDim → H) (hψ : Orthonormal ℂ ψ) (i : mDim) :
    iota (M := M) (ψ := ψ) hψ (EuclideanSpace.basisFun mDim ℂ i) = ψ i := by
  classical
  have h :=
    congrArg (fun f => f (EuclideanSpace.basisFun mDim ℂ i)) (iota_toLinearMap (M := M) (ψ := ψ) hψ)
  exact h.trans (iotaLin_apply_basisFun (M := M) (ψ := ψ) i)

lemma iota_apply_single_one (ψ : mDim → H) (hψ : Orthonormal ℂ ψ) (i : mDim) :
    iota (M := M) (ψ := ψ) hψ (EuclideanSpace.single i (1 : ℂ)) = ψ i := by
  classical
  simpa [EuclideanSpace.basisFun_apply] using iota_apply_basisFun (M := M) (ψ := ψ) hψ i

/-- Rank-one operator `x ⊗ x : y ↦ ⟪x,y⟫ • x`. -/
noncomputable def rankOneCLM (x : H) : H →L[ℂ] H :=
  (ContinuousLinearMap.toSpanSingleton ℂ x).comp (innerSL ℂ x)

@[simp] lemma rankOneCLM_apply (x z : H) : rankOneCLM (x := x) z = (inner ℂ x z) • x := by
  simp [rankOneCLM]

lemma inner_rankOneCLM (x y z : H) :
    inner ℂ y (rankOneCLM (x := x) z) = inner ℂ x z * inner ℂ y x := by
  simp [rankOneCLM_apply]

lemma inner_eq_conj_swap (x y : H) : inner ℂ x y = conj (inner ℂ y x) := by
  -- `inner_conj_symm` is stated using the `⟪·,·⟫` notation, but it is definitionally `inner`.
  simpa using (inner_conj_symm (𝕜 := ℂ) (x := x) (y := y)).symm

/-- “RKHS prime operator” built from vectors `k n` (finite sum, since `Nodes K` is finite). -/
noncomputable def T_P_RKHS_like (k : Q3.Nodes K → H) : H →L[ℂ] H :=
  ∑ n : Q3.Nodes K,
    ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) • rankOneCLM (x := k n)

lemma toEuclideanLin_apply_basisFun (A : Matrix mDim mDim ℂ) (i j : mDim) :
    (Matrix.toEuclideanLin A (EuclideanSpace.basisFun mDim ℂ j)) i = A i j := by
  classical
  -- `basisFun j = single j 1 = toLp _ (Pi.single j 1)` and `A *ᵥ Pi.single j 1 = A.col j`.
  simp [Matrix.toEuclideanLin_apply, EuclideanSpace.basisFun_apply]

/-- Nontrivial compression identity (`hA`): under the evaluation-matching hypothesis,
`T_P_comp` is exactly the compression of the RKHS-like operator. -/
theorem T_P_comp_toCLM_eq_compression
    (ψ : mDim → H) (hψ : Orthonormal ℂ ψ)
    (k : Q3.Nodes K → H)
    (h_eval : ∀ (n : Q3.Nodes K) (i : mDim),
      inner ℂ (ψ i) (k n) = Q3.prime_vec M (Q3.xi_n n) i) :
    (Matrix.toEuclideanLin (Q3.T_P_comp K B t M)).toContinuousLinearMap =
      compression (ι := iota (M := M) (ψ := ψ) hψ)
        (T := T_P_RKHS_like (K := K) (B := B) (t := t) (k := k)) := by
  classical
  -- First show equality at the level of linear maps (basis-vector extensionality).
  have hlin :
      Matrix.toEuclideanLin (Q3.T_P_comp K B t M) =
        ((compression (ι := iota (M := M) (ψ := ψ) hψ)
            (T := T_P_RKHS_like (K := K) (B := B) (t := t) (k := k))) : E →ₗ[ℂ] E) := by
    apply (EuclideanSpace.basisFun mDim ℂ).toBasis.ext
    intro j
    ext i
    -- Left: matrix entry.
    have hL :
        (Matrix.toEuclideanLin (Q3.T_P_comp K B t M) (EuclideanSpace.basisFun mDim ℂ j)) i =
          Q3.T_P_comp K B t M i j := by
      simpa using
        (toEuclideanLin_apply_basisFun (M := M) (A := Q3.T_P_comp K B t M) i j)
    -- Right: compute the `i`-th coordinate via `⟪basisFun i, ·⟫`.
    have hR :
        ((compression (ι := iota (M := M) (ψ := ψ) hψ)
              (T := T_P_RKHS_like (K := K) (B := B) (t := t) (k := k)))
            (EuclideanSpace.basisFun mDim ℂ j)) i =
          Q3.T_P_comp K B t M i j := by
      -- Coordinate extraction using the orthonormal basis.
      have hcoord :
          ((compression (ι := iota (M := M) (ψ := ψ) hψ)
                (T := T_P_RKHS_like (K := K) (B := B) (t := t) (k := k)))
              (EuclideanSpace.basisFun mDim ℂ j)) i =
            inner ℂ (EuclideanSpace.basisFun mDim ℂ i)
              ((compression (ι := iota (M := M) (ψ := ψ) hψ)
                    (T := T_P_RKHS_like (K := K) (B := B) (t := t) (k := k)))
                  (EuclideanSpace.basisFun mDim ℂ j)) := by
        simpa using
          (EuclideanSpace.basisFun_inner (𝕜 := ℂ) (ι := mDim)
              ((compression (ι := iota (M := M) (ψ := ψ) hψ)
                  (T := T_P_RKHS_like (K := K) (B := B) (t := t) (k := k)))
                (EuclideanSpace.basisFun mDim ℂ j)) i).symm
      -- Expand the compression and the RKHS-like operator.
      -- After simplifying `ι(basisFun i) = ψ i` and `ι(basisFun j) = ψ j`, we match `T_P_comp`.
      rw [hcoord]
      have hswap : ∀ n : Q3.Nodes K, inner ℂ (k n) (ψ j) = conj (inner ℂ (ψ j) (k n)) := by
        intro n
        -- `inner_conj_symm` is `conj (inner y x) = inner x y`.
        simpa using (inner_conj_symm (𝕜 := ℂ) (x := k n) (y := ψ j)).symm
      simp [compression, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        iota_apply_single_one (M := M) (ψ := ψ) hψ, T_P_RKHS_like, inner_rankOneCLM,
        hswap, h_eval, Q3.T_P_comp, mul_assoc, mul_left_comm, mul_comm]
    exact hL.trans hR.symm
  -- Upgrade the linear-map equality to an equality of continuous linear maps.
  ext x i
  have hx := congrArg (fun f => f x) hlin
  simpa using congrArg (fun y => y i) hx

/-! ### BasisFun model (machine-friendly `h_eval`) -/

section BasisFunModel

noncomputable def psi_basis : mDim → E :=
  fun i => EuclideanSpace.basisFun mDim ℂ i

noncomputable def k_basis : Q3.Nodes K → E :=
  fun n => (EuclideanSpace.equiv mDim ℂ).symm (fun i => Q3.prime_vec M (Q3.xi_n n) i)

lemma psi_basis_orthonormal : Orthonormal ℂ (psi_basis (M := M)) := by
  classical
  change Orthonormal ℂ (fun i => EuclideanSpace.basisFun mDim ℂ i)
  exact (EuclideanSpace.basisFun mDim ℂ).orthonormal

lemma h_eval_basisFun :
    ∀ (n : Q3.Nodes K) (i : mDim),
      inner ℂ (psi_basis (M := M) i) (k_basis (K := K) (M := M) n) =
        Q3.prime_vec M (Q3.xi_n n) i := by
  classical
  intro n i
  simpa [psi_basis, k_basis] using
    (EuclideanSpace.basisFun_inner (𝕜 := ℂ) (ι := mDim)
      (x := k_basis (K := K) (M := M) n) i)

/-- With `ψ = basisFun` and `k n = prime_vec`, the compression identity is by simp. -/
lemma T_P_comp_toCLM_eq_compression_basisFun :
    (Matrix.toEuclideanLin (Q3.T_P_comp K B t M)).toContinuousLinearMap =
      compression (ι := iota (H := E) (M := M) (ψ := psi_basis (M := M))
          (psi_basis_orthonormal (M := M)))
        (T := T_P_RKHS_like (H := E) (K := K) (B := B) (t := t)
          (k := k_basis (K := K) (M := M))) := by
  classical
  simpa using
    (T_P_comp_toCLM_eq_compression (H := E) (K := K) (B := B) (t := t) (M := M)
      (ψ := psi_basis (M := M)) (hψ := psi_basis_orthonormal (M := M))
      (k := k_basis (K := K) (M := M)) (h_eval := h_eval_basisFun (K := K) (M := M)))

/-- OpNorm bound via basisFun compression: `‖T_P_comp‖ ≤ ‖T_P_RKHS_like‖`. -/
lemma T_P_comp_opNorm_le_basisFun :
    ‖(Matrix.toEuclideanLin (Q3.T_P_comp K B t M)).toContinuousLinearMap‖ ≤
      ‖T_P_RKHS_like (H := E) (K := K) (B := B) (t := t)
          (k := k_basis (K := K) (M := M))‖ := by
  classical
  let ι :=
    iota (H := E) (M := M) (ψ := psi_basis (M := M)) (psi_basis_orthonormal (M := M))
  let T :=
    T_P_RKHS_like (H := E) (K := K) (B := B) (t := t) (k := k_basis (K := K) (M := M))
  have hC1 : ‖compression (ι := ι) T‖ ≤ ‖T‖ :=
    Q3.Proofs.C1Embedding.compression_opNorm_le (ι := ι) (T := T)
  have hA :
      (Matrix.toEuclideanLin (Q3.T_P_comp K B t M)).toContinuousLinearMap =
        compression (ι := ι) T := by
    simpa [ι, T] using
      (T_P_comp_toCLM_eq_compression_basisFun (K := K) (B := B) (t := t) (M := M))
  simpa [hA] using hC1

end BasisFunModel

end RKHSInterfaceC1
end Q3.Proofs
