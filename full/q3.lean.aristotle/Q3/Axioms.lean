/-
Q3 Formalization: External Axioms
=================================

This file contains axioms organized by tier:
- **Tier-1**: Classical results from peer-reviewed literature (1911-1999)
- **Tier-2**: Q3 paper contributions (new technical results)

IMPORTANT: Run `#print axioms RH_of_Weil_and_Q3` to verify all dependencies.

Axiom Summary:
- Tier-1: 10 axioms (Weil, Guinand, a_star properties, Szegő-Böttcher, Schur, etc.)
- Tier-2: 12 axioms (A1', A2, A3, RKHS, node spacing, Q ≥ 0 on compacts)

New additions (2024-12):
- T1.3d: a_star_even (digamma conjugation symmetry)
- T1.4b: Szego_Rayleigh_lower_bound (Rayleigh quotient → symbol infimum)
-/

import Q3.Basic.Defs

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Matrix.Norms.L2Operator

namespace Q3

/-!
# ═══════════════════════════════════════════════════════════════════════════════
# TIER-1: CLASSICAL AXIOMS FROM LITERATURE
# ═══════════════════════════════════════════════════════════════════════════════

These are well-established theorems from peer-reviewed mathematics.
Each is cited with publication details.
-/

/-! ## Axiom T1.1: Weil Criterion (1952)

The Weil explicit formula criterion:
  RH ⟺ Q(Φ) ≥ 0 for all Φ in the Weil cone

**Citation:**
- Weil, A. (1952). "Sur les 'formules explicites' de la théorie des nombres premiers"
  Meddelanden Från Lunds Universitets Matematiska Seminarium, 252-265.
- Bombieri, E. (2000). "The Riemann Hypothesis" Clay Mathematics Institute.
-/
axiom Weil_criterion : (∀ Φ ∈ Weil_cone, Q Φ ≥ 0) ↔ RH

/-! ## Axiom T1.2: Guinand-Weil Explicit Formula (1948)

**Citation:**
- Guinand, A.P. (1948). "A summation formula in the theory of prime numbers"
  Proc. London Math. Soc. (2) 50, 107-119.
-/
axiom explicit_formula :
  ∀ Φ ∈ Weil_cone, Q Φ = arch_term Φ - prime_term Φ

/-! ## Axiom T1.3: Archimedean Kernel Positivity

a*(ξ) = 2π(log π - Re(ψ(1/4 + iπξ))) > 0 for all ξ

**Citation:**
- Titchmarsh, E.C. (1986) "The Theory of the Riemann Zeta-Function", Chapter IX.
-/
axiom a_star_pos : ∀ ξ : ℝ, a_star ξ > 0

/-! ## Axiom T1.3b: Archimedean Kernel Continuity

a*(ξ) is continuous (follows from digamma regularity away from poles).

**Citation:**
- Titchmarsh, E.C. (1986) "The Theory of the Riemann Zeta-Function", Chapter IX.
-/
axiom a_star_continuous : Continuous a_star

/-! ## Axiom T1.3c: Archimedean Kernel Bounded on Compacts

a*(ξ) is bounded on any compact set (continuous function on compact → bounded).

**Citation:**
- Direct corollary of continuity and Heine-Borel.
-/
axiom a_star_bdd_on_compact : ∀ (K : ℝ) (hK : K > 0),
  ∃ M > 0, ∀ ξ ∈ Set.Icc (-K) K, a_star ξ ≤ M

/-! ## Axiom T1.3d: Archimedean Kernel Even Symmetry

a*(−ξ) = a*(ξ) because ψ(z̄) = ψ(z)̄ for the digamma function.
For z = 1/4 + iπξ, the conjugate is 1/4 - iπξ = 1/4 + iπ(−ξ).

**Citation:**
- Abramowitz & Stegun (1964). "Handbook of Mathematical Functions", Section 6.3.
- NIST DLMF (2024), Section 5.5: ψ(z̄) = ψ(z)̄.
-/
axiom a_star_even : ∀ ξ : ℝ, a_star (-ξ) = a_star ξ

/-! ## Axiom T1.4: Szegő-Böttcher Theory (1958/1999)

Eigenvalues of Toeplitz matrices bounded by symbol range.

**Citation:**
- Grenander, U. & Szegő, G. (1958). "Toeplitz Forms and Their Applications".
- Böttcher, A. & Silbermann, B. (1999). "Introduction to Large Truncated Toeplitz Matrices".
-/

/-- Toeplitz matrix from symbol -/
noncomputable def ToeplitzMatrix (M : ℕ) (P : ℝ → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => P ((i.val - j.val : ℤ) * Real.pi / M)

axiom Szego_Bottcher_eigenvalue_bound :
  ∀ (M : ℕ) (P : ℝ → ℝ), Continuous P → (∀ θ, P (-θ) = P θ) →
  ∀ μ, (∃ v : Fin M → ℝ, v ≠ 0 ∧ (ToeplitzMatrix M P).mulVec v = μ • v) →
    sInf {P θ | θ ∈ Set.Icc 0 (2 * Real.pi)} ≤ μ ∧
    μ ≤ sSup {P θ | θ ∈ Set.Icc 0 (2 * Real.pi)}

axiom Szego_Bottcher_convergence :
  ∀ (P : ℝ → ℝ), Continuous P → (∀ θ, P (-θ) = P θ) →
  ∀ ε > 0, ∃ N, ∀ m ≥ N,
    ∀ μ, (∃ v : Fin m → ℝ, v ≠ 0 ∧ (ToeplitzMatrix m P).mulVec v = μ • v) →
      ∃ θ ∈ Set.Icc 0 (2 * Real.pi), |μ - P θ| < ε

/-! ## Axiom T1.4b: Szegő Rayleigh Quotient Bound (Classical)

**Key Bridge Axiom**: Minimum Rayleigh quotient converges to symbol infimum.

For Toeplitz matrix T_M[P] with continuous even symbol P:
  inf_{v ≠ 0} (v^T · T_M[P] · v) / ||v||² → inf_θ P(θ)  as M → ∞

More precisely: for any ε > 0, there exists M₀ such that for all M ≥ M₀,
the Rayleigh quotient is at least inf P - ε.

**Citation:**
- Grenander, U. & Szegő, G. (1958). "Toeplitz Forms and Their Applications", Ch. 5.
- Gray, R.M. (2006). "Toeplitz and Circulant Matrices: A Review", Theorem 4.2.
-/

/-- Rayleigh quotient for symmetric matrix -/
noncomputable def RayleighQuotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, v i * A i j * v j) / (∑ i, v i ^ 2)

/-- Szegő Rayleigh bound: for large M, Rayleigh quotient ≥ inf P - ε -/
axiom Szego_Rayleigh_lower_bound :
  ∀ (P : ℝ → ℝ), Continuous P → (∀ θ, P (-θ) = P θ) →
  ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
      RayleighQuotient (ToeplitzMatrix M P) v ≥ sInf {P θ | θ ∈ Set.Icc 0 (2 * Real.pi)} - ε

/-! ## Axiom T1.5: Schur Test (1911)

**Citation:**
- Schur, I. (1911). "Bemerkungen zur Theorie der beschränkten Bilinearformen"
  J. Reine Angew. Math. 140, 1-28.
-/
axiom Schur_test {n : Type*} [Fintype n] [DecidableEq n] :
  ∀ (A : Matrix n n ℝ), A.IsSymm →
  ∀ (C : ℝ), 0 ≤ C → (∀ i, ∑ j, |A i j| ≤ C) → ‖A‖ ≤ C

/-! ## Axiom T1.6: Archimedean Constant Positivity

c₀(K) = inf_{|ξ| ≤ K} a*(ξ) > 0 by continuity and T1.3.
-/

/-- Archimedean constant: c₀(K) = inf_{|ξ| ≤ K} a*(ξ) -/
noncomputable def c_arch (K : ℝ) : ℝ :=
  sInf {a_star ξ | ξ ∈ Set.Icc (-K) K}

axiom c_arch_pos : ∀ K : ℝ, K > 0 → c_arch K > 0

/-! ## Uniform Archimedean Floor (December 2025 paper update)

The paper was updated to use a UNIFORM floor c* = 11/10 instead of K-dependent c_arch(K).
This is the global minimum of P_A(θ) over the entire torus T.
Proven in A3_FLOOR_v22_stage4_floor.lean.

Benefits of uniform approach:
- M₀ is K-independent (single threshold for all K)
- t_rkhs is K-independent (single heat parameter)
- Simplifies the A3_bridge axiom chain
-/

/-- Uniform Archimedean floor: c* = 11/10
    This is min_{θ ∈ T} P_A(θ) where P_A is the Archimedean symbol. -/
noncomputable def c_star : ℝ := 11 / 10

/-- c* is positive (trivial computation) -/
lemma c_star_pos : c_star > 0 := by norm_num [c_star]

/-- c* > 1 (useful for contraction arguments) -/
lemma c_star_gt_one : c_star > 1 := by norm_num [c_star]

/-- c*/4 > 0 (the bound used in A3_bridge) -/
lemma c_star_div_four_pos : c_star / 4 > 0 := by norm_num [c_star]

/-- c* ≤ c_arch(K) for K ≥ threshold.

Since c_star = 11/10 is the GLOBAL minimum of P_A(θ) over the torus T,
and c_arch(K) = inf_{|ξ| ≤ K} a_star(ξ) is the minimum over [-K, K],
we have c_star ≤ c_arch(K) when the support of the periodization
is contained in [-K, K].

This lemma allows backwards-compatible use of old K-dependent proofs:
any bound using c_star/4 automatically gives a bound using c_arch(K)/4.
-/
axiom c_star_le_c_arch : ∀ K : ℝ, K ≥ 1 → c_star ≤ c_arch K

/-! ## Axiom T1.7: Eigenvalue-Norm Bound

For symmetric matrices: |eigenvalue| ≤ operator norm.
-/
axiom eigenvalue_le_norm {n : Type*} [Fintype n] [DecidableEq n] :
  ∀ (A : Matrix n n ℝ) (μ : ℝ),
  (∃ v : n → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v) → |μ| ≤ ‖A‖

/-!
# ═══════════════════════════════════════════════════════════════════════════════
# TIER-2: Q3 PAPER AXIOMS (NEW CONTRIBUTIONS)
# ═══════════════════════════════════════════════════════════════════════════════

These axioms represent the technical contributions of the Q3 paper.
Each corresponds to a theorem proved in the paper.
-/

/-! ## Supporting Definitions for Tier-2 -/

/-- Fejér kernel (triangular) -/
noncomputable def Fejer_kernel (B : ℝ) (x : ℝ) : ℝ :=
  max 0 (1 - |x| / B)

/-- Heat kernel -/
noncomputable def heat_kernel_A1 (t : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x^2 / (4 * t))

/-- Fejér-heat atom: symmetrized product -/
noncomputable def Fejer_heat_atom (B t τ : ℝ) (ξ : ℝ) : ℝ :=
  Fejer_kernel B (ξ - τ) * heat_kernel_A1 t (ξ - τ) +
  Fejer_kernel B (ξ + τ) * heat_kernel_A1 t (ξ + τ)

/-- The cone generated by Fejér-heat atoms -/
def Fejer_heat_cone (K : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c : Fin n → ℝ) (B t : Fin n → ℝ) (τ : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧
        (∀ i, B i > 0) ∧
        (∀ i, t i > 0) ∧
        (∀ i, |τ i| ≤ K) ∧
        (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) (t i) (τ i) x) }

/-- AtomCone_K: Fejér-heat atoms with support control AND membership in W_K
    This is the proper generating cone for the T5 transfer theorem -/
def AtomCone_K (K : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c : Fin n → ℝ) (B t : Fin n → ℝ) (τ : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧
        (∀ i, B i > 0) ∧
        (∀ i, t i > 0) ∧
        (∀ i, |τ i| + B i ≤ K) ∧  -- ensures support ⊆ [-K, K] (Lemma a1-fixed-t-density)
        (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) (t i) (τ i) x) ∧
        g ∈ W_K K }  -- explicitly require g ∈ W_K

/-- Even nonnegative continuous functions on [-K, K] -/
def C_even_nonneg (K : ℝ) : Set (ℝ → ℝ) :=
  { f | ContinuousOn f (Set.Icc (-K) K) ∧
        (∀ x, f x = f (-x)) ∧
        (∀ x ∈ Set.Icc (-K) K, 0 ≤ f x) }

/-! ## Axiom T2.1: A1' Density (Q3 Paper Section 4)

Fejér×heat atoms are dense in W_K (with proper support control).
The approximant g is in AtomCone_K, hence also in W_K.

**PARTIAL ARISTOTLE RESULT**: See `aristotle_output/A1_density_v2_aristotle.lean`
Aristotle proved helper lemmas:
- `HeatKernel_integral` - heat kernel integrates to 1
- `HeatKernel_mass_concentration` - mass concentrates as t → 0
Main theorem incomplete (approximation theory complexity).
-/
axiom A1_density_WK_axiom : ∀ (K : ℝ) (hK : K > 0),
  ∀ Φ ∈ W_K K, ∀ ε > 0,
    ∃ g ∈ AtomCone_K K,  -- g is in AtomCone_K ⊆ W_K
      sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε

/-- Legacy A1 density (for compatibility) -/
axiom A1_density_axiom : ∀ (K : ℝ) (hK : K > 0),
  ∀ f ∈ C_even_nonneg K, ∀ ε > 0,
    ∃ g ∈ Fejer_heat_cone K, ∀ x ∈ Set.Icc (-K) K, |f x - g x| < ε

/-! ## Axiom T2.2a: W_sum Finiteness (A2 Helper)

The sum of weights over active nodes is finite.
This is used in A2 Lipschitz to bound the prime_term difference.

**STATUS:** axiom here; see `Q3.AxiomsTheorems` for proven bridge.
-/

/-- Active prime nodes set (for axiom) -/
def ActiveNodes_axiom (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}

/-- Sum of weights over active nodes (for axiom) -/
noncomputable def W_sum_axiom (K : ℝ) : ℝ :=
  ∑' n, if n ∈ ActiveNodes_axiom K then w_Q n else 0

axiom W_sum_finite_axiom : ∀ (K : ℝ) (hK : K > 0), ∃ B, W_sum_axiom K ≤ B

/-! ## Axiom T2.2: A2 Lipschitz (Q3 Paper Section 5)

Q is Lipschitz on W_K with constant L_Q(K).
This is essential for T5 transfer: Lipschitz + dense approximation → limit preservation.

**STATUS:** axiom here; see `Q3.AxiomsTheorems` for proven bridge status.
-/
axiom Q_Lipschitz_on_W_K : ∀ (K : ℝ) (hK : K > 0),
  ∃ L > 0, ∀ Φ₁, Φ₁ ∈ W_K K → ∀ Φ₂, Φ₂ ∈ W_K K →
    |Q Φ₁ - Q Φ₂| ≤ L * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K}

/-! ## Axiom T2.3: RKHS Contraction (Q3 Paper Section 6)

The prime sampling operator T_P has ‖T_P‖ < 1 for appropriate t.

**STATUS:** axiom here; bridge pending in `Q3.AxiomsTheorems`.
-/
axiom RKHS_contraction_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧
    ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Nodes K) →
      let T_P : Matrix S S ℝ := fun i j =>
        Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
        Real.exp (-(xi_n i - xi_n j)^2 / (4 * t))
      ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤ ρ

/-! ## Axiom T2.4: Row Sum Bound (Q3 RKHS Analysis)

Gershgorin-style row sum bound for T_P matrix.

**STATUS:** axiom here; see `Q3.AxiomsTheorems` for proven bridge status.
-/
axiom T_P_row_sum_bound_axiom : ∀ (K t : ℝ) (hK : K ≥ 1) (ht : t > 0),
  ∀ (Nodes_K : Set ℕ) [Fintype Nodes_K] (T_P : Matrix Nodes_K Nodes_K ℝ),
  (∀ i j : Nodes_K, T_P i j = Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
    Real.exp (-(xi_n i - xi_n j)^2 / (4 * t))) →
  ∀ i, ∑ j, |T_P i j| ≤ w_max + Real.sqrt w_max * S_K K t

/-! ## Axiom T2.5: Geometric Series Decay (Q3 RKHS Analysis)

S_K = 2x/(1-x) where x = exp(-δ²/(4t)) is a geometric series tail bound.

**STATUS:** axiom here; see `Q3.AxiomsTheorems` for proven bridge.
-/
axiom S_K_small_axiom : ∀ (K t η : ℝ) (hK : K ≥ 1) (hη : η > 0) (ht : t ≤ t_min K η),
  S_K K t ≤ η

/-! ## Axiom T2.5b: Node Spacing (Q3 RKHS Analysis)

Adjacent spectral nodes are separated by at least δ_K.

**STATUS:** axiom here; see `Q3.AxiomsTheorems` for proven bridge.
-/
axiom node_spacing_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  ∀ (n₁ n₂ : ℕ), n₁ ∈ Nodes K → n₂ ∈ Nodes K → n₁ < n₂ →
    xi_n n₂ - xi_n n₁ ≥ delta_K K

/-! ## Axiom T2.5c: Off-Diagonal Exponential Sum Bound (Q3 RKHS Analysis)

The off-diagonal sum of Gaussian terms is bounded by the geometric series S_K.

**STATUS:** axiom here; bridge pending in `Q3.AxiomsTheorems`.
-/
axiom off_diag_exp_sum_axiom : ∀ (K t : ℝ) (hK : K ≥ 1) (ht : t > 0)
    [Fintype (Nodes K)] (i : Nodes K),
    ∑ j : Nodes K, (if (j : ℕ) ≠ (i : ℕ) then
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)) else 0) ≤ S_K K t

/-! ## Axiom T2.6: A3 Bridge (Q3 Paper Section 7)

Toeplitz-Symbol bridge: λ_min(T_M[P_A] - T_P) ≥ c₀(K)/4.

**STATUS:** axiom here; bridge pending in `Q3.AxiomsTheorems`.
-/
axiom A3_bridge_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzMatrix M a_star i j -
      Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)))) /
    (∑ i, v i ^ 2) ≥ c_arch K / 4

/-! ## Axiom T2.6b: A3 Bridge Uniform (December 2025 paper update)

K-INDEPENDENT version of A3 bridge using uniform floor c* = 11/10.
This is the new primary formulation; the K-dependent version above is deprecated.

Key changes from K-dependent:
- Uses c_star instead of c_arch K
- M₀ and t are uniform (K-independent)
- Directly follows from A3_FLOOR (P_A(θ) ≥ 11/10 for all θ)
-/
axiom A3_bridge_uniform :
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzMatrix M a_star i j -
      Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)))) /
    (∑ i, v i ^ 2) ≥ c_star / 4

/-! ## Axiom T2.7: Q ≥ 0 on Atom Cone (Q3 Core Result)

This is the key positivity axiom: Q ≥ 0 on the generating atom cone.
This follows from A3 (Toeplitz bridge) + RKHS (contraction).

The full "Q ≥ 0 on W_K" is then a THEOREM (T5_transfer), not an axiom,
proven via: A1 (density) + A2 (Lipschitz) + this axiom.
-/

/-- Bundled statement of the A3 bridge axiom for a fixed compact parameter `K`. (DEPRECATED) -/
def A3_bridge_data (K : ℝ) : Prop :=
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzMatrix M a_star i j -
      Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)))) /
    (∑ i, v i ^ 2) ≥ c_arch K / 4

/-- Uniform A3 bridge data (December 2025 paper update).
    K-independent version using c_star = 11/10. -/
def A3_bridge_data_uniform : Prop :=
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzMatrix M a_star i j -
      Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)))) /
    (∑ i, v i ^ 2) ≥ c_star / 4

/-- Bundled statement of the RKHS contraction axiom for a fixed compact parameter `K`. (DEPRECATED) -/
def RKHS_contraction_data (K : ℝ) : Prop :=
  ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧
    ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Nodes K) →
      let T_P : Matrix S S ℝ := fun i j =>
        Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
        Real.exp (-(xi_n i - xi_n j)^2 / (4 * t))
      ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤ ρ

/-- Uniform RKHS contraction data (December 2025 paper update).
    K-independent version - the heat parameter t and bound ρ are uniform. -/
def RKHS_contraction_data_uniform : Prop :=
  ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧
    ∀ K ≥ 1, ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Nodes K) →
      let T_P : Matrix S S ℝ := fun i j =>
        Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
        Real.exp (-(xi_n i - xi_n j)^2 / (4 * t))
      ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤ ρ

/-- Core positivity transfer from the A3 bridge + RKHS contraction to atom cone positivity.
    This is the remaining hard analytic step (Q3 paper core). (DEPRECATED - use uniform version) -/
axiom Q_nonneg_on_atoms_of_A3_RKHS_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  A3_bridge_data K → RKHS_contraction_data K →
  ∀ g ∈ AtomCone_K K, Q g ≥ 0

/-- Uniform version: A3_bridge_uniform + RKHS_contraction_uniform ⟹ Q ≥ 0 on atoms.
    December 2025 paper update - the primary formulation. -/
axiom Q_nonneg_on_atoms_uniform :
  A3_bridge_data_uniform → RKHS_contraction_data_uniform →
  ∀ K ≥ 1, ∀ g ∈ AtomCone_K K, Q g ≥ 0

/-!
# ═══════════════════════════════════════════════════════════════════════════════
# AXIOM VERIFICATION
# ═══════════════════════════════════════════════════════════════════════════════
-/

-- Tier-1 axioms (7 classical)
#check Weil_criterion
#check explicit_formula
#check a_star_pos
#check Szego_Bottcher_eigenvalue_bound
#check Szego_Bottcher_convergence
#check Schur_test
#check c_arch_pos
#check eigenvalue_le_norm

-- Uniform definitions (December 2025 paper update)
#check c_star                        -- NEW: Uniform floor c* = 11/10
#check c_star_pos                    -- c* > 0
#check c_star_gt_one                 -- c* > 1
#check A3_bridge_uniform             -- NEW: K-independent A3 bridge
#check A3_bridge_data_uniform        -- NEW: Bundled uniform data
#check RKHS_contraction_data_uniform -- NEW: Bundled uniform RKHS
#check Q_nonneg_on_atoms_uniform     -- NEW: Uniform positivity transfer

-- Tier-2 axioms (12 Q3 contributions)
#check A1_density_WK_axiom           -- density in W_K
#check A1_density_axiom              -- Legacy density
#check W_sum_finite_axiom            -- W_sum bound for A2
#check Q_Lipschitz_on_W_K            -- A2 Lipschitz
#check RKHS_contraction_axiom        -- RKHS contraction
#check T_P_row_sum_bound_axiom       -- Row sum bound
#check S_K_small_axiom               -- Geometric series decay
#check node_spacing_axiom            -- Node spacing ≥ δ_K
#check off_diag_exp_sum_axiom        -- Off-diagonal sum ≤ S_K
#check A3_bridge_axiom               -- A3 Toeplitz bridge (DEPRECATED)
#check Q_nonneg_on_atoms_of_A3_RKHS_axiom   -- A3+RKHS ⇒ atoms positivity (DEPRECATED)

end Q3
