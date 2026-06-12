/-
# PO3a.4 — Outer-Invariance Minimal Bridge

We prove that the rank-1 operator equation
  -|a⟩⟨c| + |s·a - b⟩⟨d| = 0
with a ≠ 0 and d ≠ 0 forces scalar rigidity:
  b = λ • a,  c = μ • d,  λ + μ = s.

This is the algebraic core of the outer-invariance theorem for sign-split
Hilbert spaces, showing that nontrivial outer operators U, V collapse to the
identity-outer case when they are locally injective and sign-preserving.
-/
import Mathlib

open InnerProductSpace

set_option maxHeartbeats 8000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
If d ≠ 0, there exists v with ⟪d, v⟫_ℝ ≠ 0.
-/
lemma exists_inner_ne_zero {d : E} (hd : d ≠ 0) : ∃ v : E, @inner ℝ E _ d v ≠ 0 := by
  exact ⟨ d, by simpa [ inner_self_eq_norm_sq_to_K ] using hd ⟩

/-
If ⟪c, v⟫ = 0 whenever ⟪d, v⟫ = 0, and d ≠ 0, then c ∈ span{d},
    i.e., c = μ • d for some scalar μ.
-/
lemma mem_span_of_inner_vanishing {c d : E} (hd : d ≠ 0)
    (h : ∀ v : E, @inner ℝ E _ d v = 0 → @inner ℝ E _ c v = 0) :
    ∃ mu : ℝ, c = mu • d := by
  -- Decompose $c$ into its component along $d$ and its orthogonal part: $c = \mu d + w$ with $\langle d, w \rangle = 0$.
  obtain ⟨mu, w, hw⟩ : ∃ mu : ℝ, ∃ w : E, c = mu • d + w ∧ ⟪d, w⟫_ℝ = 0 := by
    refine' ⟨ ⟪d, c⟫_ℝ / ‖d‖ ^ 2, c - ( ⟪d, c⟫_ℝ / ‖d‖ ^ 2 ) • d, _, _ ⟩ <;> simp_all +decide [ norm_smul ];
    simp +decide [ inner_sub_right, inner_smul_right, hd ];
  specialize h w hw.2; simp_all +decide [ inner_add_left, inner_smul_left ] ;

/-
Core algebraic lemma (rank-one vanishing).

If a ≠ 0, d ≠ 0, and the rank-1 operator equation
  ∀ v, -⟪c, v⟫ • a + ⟪d, v⟫ • (s • a - b) = 0
holds, then there exist scalars λ, μ with
  b = λ • a,  c = μ • d,  λ + μ = s.
-/
theorem rank_one_vanishing
    {a b c d : E} {s : ℝ}
    (ha : a ≠ 0) (hd : d ≠ 0)
    (hK : ∀ v : E, -@inner ℝ E _ c v • a + @inner ℝ E _ d v • (s • a - b) = (0 : E)) :
    ∃ lam mu : ℝ, b = lam • a ∧ c = mu • d ∧ lam + mu = s := by
  -- From hK, taking v with ⟪d, v⟫ = 0, we get ⟪c, v⟫ • a = 0. Since a ≠ 0, ⟪c, v⟫ = 0. So ∀ v, ⟪d, v⟫ = 0 → ⟪c, v⟫ = 0.
  have h_inner_zero : ∀ v : E, ⟪d, v⟫_ℝ = 0 → ⟪c, v⟫_ℝ = 0 := by
    intro v hv; specialize hK v; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
  -- By `mem_span_of_inner_vanishing`, ∃ mu, c = mu • d.
  obtain ⟨mu, hmu⟩ : ∃ mu : ℝ, c = mu • d := by
    exact?;
  -- Substitute c = mu • d into hK: ∀ v, -mu * ⟪d, v⟫ • a + ⟪d, v⟫ • (s • a - b) = 0, i.e., ∀ v, ⟪d, v⟫ • (-mu • a + s • a - b) = 0.
  have h_subst : ∀ v : E, ⟪d, v⟫_ℝ • (-mu • a + s • a - b) = 0 := by
    simp_all +decide [ inner_smul_left, smul_add, smul_sub ];
    convert hK using 2 ; simp +decide [ mul_comm, smul_smul ] ; abel_nf;
  -- By `exists_inner_ne_zero`, ∃ v with ⟪d, v⟫ ≠ 0. So -mu • a + s • a - b = 0, i.e., b = (s - mu) • a.
  obtain ⟨v, hv⟩ : ∃ v : E, ⟪d, v⟫_ℝ ≠ 0 := by
    exact?
  have hb : b = (s - mu) • a := by
    specialize h_subst v; simp_all +decide [ sub_smul ] ;
    grind;
  exact ⟨ s - mu, mu, hb, hmu, by ring ⟩

/-!
## Application to outer-operator rigidity

We now show that the abstract rank-one vanishing result implies the full
outer-invariance rigidity theorem for the sign-split Hilbert space setting.

Given:
- Vectors hp, xp (the "positive" vectors) and hm, xm (the "negative" vectors)
  in a real inner product space, with hp ≠ 0 and hm ≠ 0
- Continuous linear maps Ustar, Vstar
- Ustar injective on span{hp, xp}, Vstar injective on span{hm, xm}
- The "receiver" K = -|Ustar hp⟩⟨Vstar xm| + |c·Ustar hp - Ustar xp⟩⟨Vstar hm| = 0

Then xp = λ • hp, xm = μ • hm, and λ + μ = c.
-/

/-
If a linear map is injective on the span of two vectors and maps one to a
    scalar multiple of the other's image, then the original vectors are proportional.
-/
lemma proportional_of_injective_on_span
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {T : E →L[ℝ] F} {u v : E} {lam : ℝ}
    (hinj : ∀ x ∈ Submodule.span ℝ ({u, v} : Set E), T x = 0 → x = 0)
    (hTv : T v = lam • T u) :
    v = lam • u := by
  rw [ ← sub_eq_zero, ← hinj ( v - lam • u ) ?_ ] <;> simp +decide [ *, Submodule.mem_span_pair ];
  exact ⟨ -lam, 1, by simp +decide [ sub_eq_neg_add ] ⟩

/-
**Outer-invariance rigidity theorem (PO3a.4).**

In a real inner product space, given vectors hp, xp, hm, xm and continuous
linear maps Ustar, Vstar, if:
1. Ustar is injective on span{hp, xp},
2. Vstar is injective on span{hm, xm},
3. hp ≠ 0 and hm ≠ 0,
4. The receiver K = -|Ustar hp⟩⟨Vstar xm| + |c · Ustar hp - Ustar xp⟩⟨Vstar hm| = 0,

then xp = λ • hp, xm = μ • hm, and λ + μ = c for some scalars λ, μ.
-/
theorem outer_invariance_rigidity
    {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {hp xp : E} {hm xm : E}
    {Ustar : E →L[ℝ] F} {Vstar : E →L[ℝ] G}
    {s : ℝ}
    (hhp : hp ≠ 0) (hhm : hm ≠ 0)
    (hUinj : ∀ x ∈ Submodule.span ℝ ({hp, xp} : Set E), Ustar x = 0 → x = 0)
    (hVinj : ∀ x ∈ Submodule.span ℝ ({hm, xm} : Set E), Vstar x = 0 → x = 0)
    (hK : ∀ v : G, -@inner ℝ G _ (Vstar xm) v • Ustar hp +
      @inner ℝ G _ (Vstar hm) v • (s • Ustar hp - Ustar xp) = (0 : F)) :
    ∃ lam mu : ℝ, xp = lam • hp ∧ xm = mu • hm ∧ lam + mu = s := by
  by_cases hUhp : Ustar hp = 0;
  · exact False.elim ( hhp ( hUinj hp ( Submodule.subset_span ( Set.mem_insert _ _ ) ) hUhp ) );
  · -- Apply the rank-one vanishing result to the equation hK.
    obtain ⟨lam, mu, hlam, hmu, hsum⟩ : ∃ lam mu : ℝ, Ustar xp = lam • Ustar hp ∧ Vstar xm = mu • Vstar hm ∧ lam + mu = s := by
      convert rank_one_vanishing hUhp _ _;
      any_goals tauto;
      rotate_left;
      exact s • Ustar hp - Ustar xp;
      · simp +decide [ inner_sub_left, inner_smul_left ];
        simp +decide [ sub_smul, smul_sub, mul_comm s ];
        intro v
        have := hK (Vstar hm)
        simp at this;
        -- By simplifying, we can see that the equation holds if and only if $Ustar xp = s • Ustar hp$.
        have h_simp : Ustar xp = (s - ⟪Vstar xm, Vstar hm⟫_ℝ / ‖Vstar hm‖ ^ 2) • Ustar hp := by
          by_cases h : ‖Vstar hm‖ = 0 <;> simp +decide [ h, sub_smul, smul_sub, div_eq_inv_mul ] at this ⊢;
          · exact absurd h ( norm_ne_zero_iff.mpr ( show Vstar hm ≠ 0 from fun h' => hhm <| hVinj hm ( Submodule.subset_span <| Set.mem_insert _ _ ) h' ) );
          · simp +decide [ ← eq_sub_iff_add_eq', ← smul_smul, h ] at this ⊢;
            simp +decide [ ← this, smul_smul, h ];
            simp +decide [ h, smul_sub, smul_smul, mul_assoc, mul_left_comm, mul_comm ];
        rw [ h_simp, inner_smul_left ] ; simp +decide [ mul_comm, smul_smul ];
      · constructor <;> intro h;
        · have := hK ( Vstar hm ) ; simp_all +decide [ inner_smul_left, inner_smul_right ] ;
          by_cases h : ‖Vstar hm‖ = 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg, smul_smul ];
          · exact absurd ( hVinj hm ( Submodule.subset_span ( Set.mem_insert _ _ ) ) h ) hhm;
          · exact smul_right_injective _ ( pow_ne_zero 2 ( norm_ne_zero_iff.mpr h ) ) ( by simpa [ mul_comm, smul_smul ] using this.symm );
        · have h_inner : ∀ v : G, ⟪Vstar xm, v⟫_ℝ = ‹ℝ› * ⟪Vstar hm, v⟫_ℝ := by
            intro v; specialize hK v; simp_all +decide [ sub_eq_iff_eq_add ] ;
            simp_all +decide [ ← eq_sub_iff_add_eq', ← smul_assoc ];
            rw [ ← hK, mul_comm ];
          refine' ext_inner_right ℝ _;
          simp +decide [ h_inner, inner_smul_left ];
    refine' ⟨ lam, mu, _, _, hsum ⟩;
    · apply proportional_of_injective_on_span hUinj hlam;
    · convert proportional_of_injective_on_span hVinj hmu using 1