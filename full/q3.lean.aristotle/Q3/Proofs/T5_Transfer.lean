/-
T5 Transfer Theorem: Q ≥ 0 on dense subset implies Q ≥ 0 on closure

This module implements the T5 transfer approach:
1. Define SpecialAtomCone_K with fixed (B_min, t_sym), varying τ
2. Prove Q ≥ 0 on SpecialAtomCone_K via A3 bridge
3. Prove SpecialAtomCone_K is dense in W_K
4. Conclude Q ≥ 0 on W_K by continuity

References:
- Q3 paper Section 5 (Transfer theorem)
- docs/PERIODIZATION_INSIGHT.md
-/

import Q3.Axioms
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.Rayleigh_Q_identification

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical
open MeasureTheory

noncomputable section

namespace Q3.Proofs.T5Transfer

-- The fixed parameters B_min = 3 and t_sym = 3/50 are defined in
-- Rayleigh_Q_identification.lean at the top level (not in namespace)

/-! ## Special Atom Cone

The SpecialAtomCone_K uses FIXED parameters (B_min, t_sym) with varying shifts τ.
This is the cone where we can prove Q ≥ 0 using the A3 floor bound.

KEY: Uses Fejer_heat_atom (SYMMETRIZED version) to match AtomCone_K.
-/

/-- Atoms with fixed bandwidth B_min and heat parameter t_sym, varying shifts τ.
    This is the generating cone for T5 transfer.
    Uses Fejer_heat_atom (symmetrized) to match Q3.AtomCone_K. -/
def SpecialAtomCone_K (K : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c : Fin n → ℝ) (τ : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧
        (∀ i, |τ i| + B_min ≤ K) ∧  -- ensures support ⊆ [-K, K]
        (∀ x, g x = ∑ i, c i * Q3.Fejer_heat_atom B_min t_sym (τ i) x) ∧
        g ∈ Q3.W_K K }  -- require W_K membership like AtomCone_K

/-- A single special atom: Fejer_heat_atom with fixed (B_min, t_sym). -/
def SpecialAtom (τ : ℝ) : ℝ → ℝ := Q3.Fejer_heat_atom B_min t_sym τ

/-! ## SpecialAtomCone_K ⊆ AtomCone_K

The key insight: SpecialAtomCone_K is a SUBSET of AtomCone_K with fixed (B_min, t_sym).
This allows us to use the Q_nonneg_on_atoms_of_A3_RKHS_axiom.
-/

/-- B_min > 0 (required for AtomCone_K membership). -/
lemma B_min_pos : B_min > 0 := by
  unfold B_min
  norm_num

/-- t_sym > 0 (required for AtomCone_K membership). -/
lemma t_sym_pos : t_sym > 0 := by
  unfold t_sym
  norm_num

/-- SpecialAtomCone_K is contained in AtomCone_K.
    This is the key inclusion that lets us use Q_nonneg_on_atoms_of_A3_RKHS_axiom. -/
theorem special_cone_subset_atom_cone (K : ℝ) :
    SpecialAtomCone_K K ⊆ Q3.AtomCone_K K := by
  intro g hg
  obtain ⟨n, c, τ, hc, hτ, hdef, hW⟩ := hg
  -- Construct the AtomCone_K witness with constant B = B_min, t = t_sym
  refine ⟨n, c, fun _ => B_min, fun _ => t_sym, τ, hc, ?_, ?_, ?_, ?_, hW⟩
  · intro i; exact B_min_pos
  · intro i; exact t_sym_pos
  · exact hτ
  · exact hdef

/-! ## Q ≥ 0 on SpecialAtomCone_K

Since SpecialAtomCone_K ⊆ AtomCone_K, and we have Q_nonneg_on_atoms_of_A3_RKHS_axiom,
we get Q ≥ 0 on SpecialAtomCone_K.
-/

/-- Q is nonnegative on SpecialAtomCone_K via inclusion in AtomCone_K.

    Uses Q_nonneg_on_atoms_of_A3_RKHS_axiom applied to the inclusion
    SpecialAtomCone_K ⊆ AtomCone_K.
-/
theorem Q_nonneg_special_cone (K : ℝ) (hK : K ≥ 1)
    (hA3 : Q3.A3_bridge_data K) (hRKHS : Q3.RKHS_contraction_data K)
    (g : ℝ → ℝ) (hg : g ∈ SpecialAtomCone_K K) :
    Q3.Q g ≥ 0 := by
  have hg' : g ∈ Q3.AtomCone_K K := special_cone_subset_atom_cone K hg
  exact Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom K hK hA3 hRKHS g hg'

/-! ## T5 Transfer: Q ≥ 0 on W_K

The key insight: we can use AtomCone_K directly (not SpecialAtomCone_K) since:
1. Q ≥ 0 on AtomCone_K (via Q_nonneg_on_atoms_of_A3_RKHS_axiom)
2. AtomCone_K is dense in W_K (via A1_density_WK_axiom)
3. Q is Lipschitz on W_K (via Q_Lipschitz_on_W_K axiom)

This is cleaner than the original approach which required SpecialAtomCone_K density.
-/

/-- Q is nonnegative on AtomCone_K. Direct application of the axiom. -/
theorem Q_nonneg_on_atom_cone (K : ℝ) (hK : K ≥ 1)
    (hA3 : Q3.A3_bridge_data K) (hRKHS : Q3.RKHS_contraction_data K)
    (g : ℝ → ℝ) (hg : g ∈ Q3.AtomCone_K K) :
    Q3.Q g ≥ 0 :=
  Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom K hK hA3 hRKHS g hg

/-- AtomCone_K membership implies W_K membership. -/
lemma atom_cone_subset_W_K (K : ℝ) : Q3.AtomCone_K K ⊆ Q3.W_K K := by
  intro g hg
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨_, hW⟩⟩ := hg
  exact hW

/-- **T5 Transfer Theorem**: Q ≥ 0 on all of W_K.

    Proof using AtomCone_K directly:
    1. Q ≥ 0 on AtomCone_K (by Q_nonneg_on_atoms_of_A3_RKHS_axiom)
    2. AtomCone_K is dense in W_K (by A1_density_WK_axiom)
    3. Q is Lipschitz continuous on W_K (by Q_Lipschitz_on_W_K axiom)
    4. Therefore Q ≥ 0 on all of W_K by density argument
-/
theorem Q_nonneg_on_W_K (K : ℝ) (hK_pos : K > 0) (hK : K ≥ 1)
    (hA3 : Q3.A3_bridge_data K) (hRKHS : Q3.RKHS_contraction_data K) :
    ∀ Φ ∈ Q3.W_K K, Q3.Q Φ ≥ 0 := by
  intro Φ hΦ
  -- Proof by contradiction: assume Q(Φ) < 0
  by_contra hQ
  push_neg at hQ
  -- Let ε = -Q(Φ) > 0
  have hε : 0 < -Q3.Q Φ := neg_pos.mpr hQ
  -- Get Lipschitz constant L > 0
  obtain ⟨L, hL_pos, hLip⟩ := Q3.Q_Lipschitz_on_W_K K hK_pos
  -- Choose δ = -Q(Φ) / (2L) > 0
  let δ := -Q3.Q Φ / (2 * L)
  have hδ : 0 < δ := by positivity
  -- By A1_density, get g ∈ AtomCone_K with ‖Φ - g‖_∞ < δ
  obtain ⟨g, hg_atom, hg_close⟩ := Q3.A1_density_WK_axiom K hK_pos Φ hΦ δ hδ
  -- g ∈ W_K since AtomCone_K ⊆ W_K
  have hg_W : g ∈ Q3.W_K K := atom_cone_subset_W_K K hg_atom
  -- Q(g) ≥ 0 by the axiom
  have hQg : Q3.Q g ≥ 0 := Q_nonneg_on_atom_cone K hK hA3 hRKHS g hg_atom
  -- Apply Lipschitz bound: |Q(Φ) - Q(g)| ≤ L · ‖Φ - g‖_∞
  have hLip_bound := hLip Φ hΦ g hg_W
  -- We have ‖Φ - g‖_∞ < δ = -Q(Φ)/(2L), so:
  -- |Q(Φ) - Q(g)| ≤ L · δ = L · (-Q(Φ)/(2L)) = -Q(Φ)/2
  -- Since Q(g) ≥ 0:
  --   Q(Φ) = Q(g) - (Q(g) - Q(Φ)) ≥ Q(g) - |Q(Φ) - Q(g)|
  --        ≥ 0 - (-Q(Φ)/2) = Q(Φ)/2
  -- So Q(Φ) ≥ Q(Φ)/2. For Q(Φ) < 0, this gives -|Q(Φ)| ≥ -|Q(Φ)|/2, contradiction!
  -- More precisely: Q(g) - Q(Φ) ≤ |Q(Φ) - Q(g)| < -Q(Φ)/2
  -- So Q(g) < Q(Φ) + (-Q(Φ)/2) = Q(Φ)/2 < 0
  -- But Q(g) ≥ 0, contradiction!
  have h_dist_bound : sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < δ := hg_close
  have h_lip_ineq : |Q3.Q Φ - Q3.Q g| ≤ L * sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} := hLip_bound
  have h_key : |Q3.Q Φ - Q3.Q g| < L * δ := by
    calc |Q3.Q Φ - Q3.Q g| ≤ L * sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} := h_lip_ineq
      _ < L * δ := by nlinarith [h_dist_bound]
  -- L * δ = L * (-Q(Φ)/(2L)) = -Q(Φ)/2
  have h_Ldelta : L * δ = -Q3.Q Φ / 2 := by
    simp only [δ]
    field_simp
  rw [h_Ldelta] at h_key
  -- |Q(Φ) - Q(g)| < -Q(Φ)/2
  -- Since Q(Φ) < 0 and Q(g) ≥ 0, we have Q(Φ) - Q(g) < 0
  -- So |Q(Φ) - Q(g)| = Q(g) - Q(Φ) = -(Q(Φ) - Q(g))
  have h_diff_neg : Q3.Q Φ - Q3.Q g < 0 := by linarith
  have h_abs_eq : |Q3.Q Φ - Q3.Q g| = Q3.Q g - Q3.Q Φ := by
    rw [abs_of_neg h_diff_neg]
    ring
  rw [h_abs_eq] at h_key
  -- Q(g) - Q(Φ) < -Q(Φ)/2
  -- Q(g) < Q(Φ) - Q(Φ)/2 = Q(Φ)/2 < 0
  have h_Qg_neg : Q3.Q g < Q3.Q Φ / 2 := by linarith
  have h_half_neg : Q3.Q Φ / 2 < 0 := by linarith
  -- But Q(g) ≥ 0, contradiction
  linarith

end Q3.Proofs.T5Transfer
