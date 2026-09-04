import Q3.Proofs.RouteB.Proposition59AlternatingLatticeCurvature

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

/-!
# Proposition 5.9 — the anchored second-mode overlap: finite identities only

Judge verdict `PROSHKA_VERDICT_GOAL058_SECOND_MODE_OVERLAP_OF_THE_XI_ROW_2026-09-04.md`,
`## CODEX DIRECTIVE`, `TASK_ID: GOAL058_P59_SECOND_MODE_OVERLAP_FINITE_IDENTITIES`.

Formalized here, and nothing else:

* `P59_REAL_EVEN_LATTICE_PAIRING`   — verdict identity (C), `Tr_m(F_v F_w) = 2π⟨v,w⟩`;
* `P59_ANCHORED_EIGENBASIS_DECOMPOSITION` — identities (A) and (B);
* `P59_SECOND_MODE_OVERLAP_LATTICE_IDENTITY` — identity (D), `2π d₂ = ℓ₁ Tr(X F₂)`;
* `P59_SECOND_MODE_CURVATURE_TRANSFER_IDENTITY` — identity (F);
* `P59_SECOND_JET_TWO_MODE_LEDGER` — identity (G), `α = a κ(ψ₂) + κ(R)`.

Every statement is an identity at a **fixed** `(L, N)`.  There is no cofinal rate claim,
no fitted polynomial, no resolvent norm, no complement floor, and no numerical constant
used as a proof step.  Nothing about the classical `Ξ` is used or claimed: the "Ξ row"
of the verdict enters only as the *sampling row of an arbitrary profile* `X : ℝ → ℝ`
(`proposition59XiSampleRow`), and `X` is never identified with anything.

Basis convention (`docs/routeB_bus/CONVENTION_CARD_GOAL058.md`, first line of the card):
rows are **FULL** mode coefficients `c_k`, `k ∈ [-N, N]`, and the pairing
`proposition59FullPairing` is the FULL Euclidean pairing `c₀d₀ + 2∑_{n≥1} c_n d_n`.
`proposition59_even_coords_pairing` is the card's exact `v₀ = c₀`, `vₙ = √2 cₙ`
translation into the EVEN orthonormal coordinates, so that "⟨v,w⟩" in the verdict and
"⟨c,d⟩" here are the same number for equal-parity rows.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace Q3.RouteB

/-! ## Window bookkeeping -/

/-- Split of a symmetric-window sum into its centre and its mirror pairs.  The
multiplicative twin `prod_erase_zero_Icc_symm` in the bridge file is stated for
`CommMonoid` and does not additivize, so this additive form is proved locally. -/
private theorem sum_Icc_symm_split (N : ℕ) (g : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g k =
      g 0 + ∑ n ∈ Finset.Icc 1 N, (g (n : ℤ) + g (-(n : ℤ))) := by
  induction N with
  | zero => simp
  | succ M ih =>
      have hset : Finset.Icc (-((M : ℤ) + 1)) ((M : ℤ) + 1) =
          insert ((M : ℤ) + 1)
            (insert (-((M : ℤ) + 1)) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have h1 : -((M : ℤ) + 1) ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
        simp only [Finset.mem_Icc, not_and, not_le]
        omega
      have h2 : ((M : ℤ) + 1) ∉
          insert (-((M : ℤ) + 1)) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc, not_or, not_and, not_le]
        constructor
        · omega
        · omega
      have hcast : ((M : ℤ) + 1) = ((M + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [show (-(((M + 1 : ℕ)) : ℤ)) = -((M : ℤ) + 1) by push_cast; ring,
        show (((M + 1 : ℕ)) : ℤ) = (M : ℤ) + 1 by push_cast; ring]
      rw [hset, Finset.sum_insert h2, Finset.sum_insert h1, ih,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      push_cast
      ring

/-! ## The FULL pairing and the even-coordinate translation of the convention card -/

/-- The FULL Euclidean pairing of two rows on the symmetric window `[-N, N]`. -/
def proposition59FullPairing (N : ℕ) (v w : ℤ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), v k * w k

/-- The EVEN orthonormal coordinates of the convention card: `v₀ = c₀`, `vₙ = √2 cₙ`. -/
def proposition59EvenCoord (c : ℤ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then c 0 else Real.sqrt 2 * c (n : ℤ)

/-- The convention card's coordinate translation, as an identity: for even rows the
Euclidean pairing in EVEN orthonormal coordinates is the FULL symmetric-window pairing
`c₀d₀ + 2∑_{n≥1} cₙdₙ`.  This is the only place the `√2` of the card appears. -/
theorem proposition59_even_coords_pairing (N : ℕ) (c e : ℤ → ℝ)
    (hc : ∀ k : ℤ, c (-k) = c k) (he : ∀ k : ℤ, e (-k) = e k) :
    ∑ n ∈ Finset.Icc 0 N, proposition59EvenCoord c n * proposition59EvenCoord e n =
      proposition59FullPairing N c e := by
  have hsplit : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 N := by
    simp only [Finset.mem_Icc, not_and, not_le]
    omega
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [hsplit, Finset.sum_insert h0]
  rw [proposition59FullPairing, sum_Icc_symm_split]
  simp only [proposition59EvenCoord]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  rw [if_neg hn0, if_neg hn0, hc (n : ℤ), he (n : ℤ)]
  have hstep : Real.sqrt 2 * c (n : ℤ) * (Real.sqrt 2 * e (n : ℤ)) =
      (Real.sqrt 2 * Real.sqrt 2) * (c (n : ℤ) * e (n : ℤ)) := by ring
  rw [hstep, hsqrt]
  ring

/-! ## The real P59 transform on the real axis, its anchor and its exact node values -/

/-- The value of the source-locked Proposition-5.9 raw transform of a **real** row, on
the real axis.  `proposition59RawTransform` is the source object; nothing is redefined. -/
def proposition59RealTransform (L : ℝ) (N : ℕ) (v : ℤ → ℝ) (x : ℝ) : ℝ :=
  (proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun k => (v k : ℂ)) ((x : ℝ) : ℂ)).re

/-- The P59 anchor `ℓ(v) = F_v(0) = √L · v 0` of the verdict's §1. -/
def proposition59Anchor (L : ℝ) (v : ℤ → ℝ) : ℝ := Real.sqrt L * v 0

theorem proposition59RealPole_zero (L : ℝ) : proposition59RealPole L 0 = 0 := by
  simp [proposition59RealPole]

/-- The exact P59 removable-node sampling formula for a real row:
`F_v(2πn/L) = √L (−1)ⁿ vₙ`.  This is `proposition59RawTransform_at_lattice`. -/
theorem proposition59RealTransform_at_realPole
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) {n : ℕ} (hn : n ≤ N) :
    proposition59RealTransform L N v (proposition59RealPole L n) =
      Real.sqrt L * (-1 : ℝ) ^ n * v (n : ℤ) := by
  have hj : (n : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    simp only [Finset.mem_Icc]
    exact ⟨by omega, by exact_mod_cast hn⟩
  have hval : proposition59RawTransform L (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun k => (v k : ℂ)) (((proposition59RealPole L n : ℝ)) : ℂ) =
      (((Real.sqrt L * (-1 : ℝ) ^ n * v (n : ℤ) : ℝ)) : ℂ) := by
    rw [proposition59RealPole_ofReal,
      proposition59RawTransform_at_lattice hL _ _ hj,
      Int.cast_negOnePow_natCast ℂ n]
    push_cast
    ring
  unfold proposition59RealTransform
  rw [hval, Complex.ofReal_re]

/-- The exact anchor value `F_v(0) = √L · v 0`. -/
theorem proposition59RealTransform_at_zero
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v : ℤ → ℝ) :
    proposition59RealTransform L N v 0 = proposition59Anchor L v := by
  have h := proposition59RealTransform_at_realPole hL N v (Nat.zero_le N)
  rw [proposition59RealPole_zero] at h
  rw [h, proposition59Anchor]
  norm_num

/-! ## The finite P59 trapezoidal lattice functional `Tr_m` -/

/-- The verdict's finite P59 trapezoidal functional
`Tr_m(f) = (2π/L)(f(0) + 2∑_{n=1}^{N} f(2πn/L))`. -/
def proposition59LatticeTrace (L : ℝ) (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  2 * Real.pi / L * (f 0 + 2 * ∑ n ∈ Finset.Icc 1 N, f (proposition59RealPole L n))

theorem proposition59LatticeTrace_add (L : ℝ) (N : ℕ) (f g : ℝ → ℝ) :
    proposition59LatticeTrace L N (fun x => f x + g x) =
      proposition59LatticeTrace L N f + proposition59LatticeTrace L N g := by
  simp only [proposition59LatticeTrace]
  rw [Finset.sum_add_distrib]
  ring

theorem proposition59LatticeTrace_sub (L : ℝ) (N : ℕ) (f g : ℝ → ℝ) :
    proposition59LatticeTrace L N (fun x => f x - g x) =
      proposition59LatticeTrace L N f - proposition59LatticeTrace L N g := by
  simp only [proposition59LatticeTrace]
  rw [Finset.sum_sub_distrib]
  ring

theorem proposition59LatticeTrace_const_mul (L : ℝ) (N : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    proposition59LatticeTrace L N (fun x => c * f x) =
      c * proposition59LatticeTrace L N f := by
  simp only [proposition59LatticeTrace]
  rw [← Finset.mul_sum]
  ring

/-- `Tr_m` only sees the finitely many included nodes: two profiles agreeing there have
the same trace. -/
theorem proposition59LatticeTrace_congr_nodes (L : ℝ) (N : ℕ) (f g : ℝ → ℝ)
    (h0 : f 0 = g 0)
    (hnode : ∀ n ∈ Finset.Icc 1 N,
      f (proposition59RealPole L n) = g (proposition59RealPole L n)) :
    proposition59LatticeTrace L N f = proposition59LatticeTrace L N g := by
  simp only [proposition59LatticeTrace]
  rw [h0, Finset.sum_congr rfl hnode]

/-! ## Item 1 — `P59_REAL_EVEN_LATTICE_PAIRING` (verdict identity (C))

`Tr_m(F_v F_w) = 2π⟨v, w⟩` for real even rows.  Pure algebra from the exact removable
sampling formula: the `√L` amplification of the two samples cancels the `2π/L` of the
trapezoid, and the alternating signs cancel pairwise. -/

/-- **Identity (C)**, `P59_REAL_EVEN_LATTICE_PAIRING`. -/
theorem proposition59_real_even_lattice_pairing
    {L : ℝ} (hL : 0 < L) (N : ℕ) (v w : ℤ → ℝ)
    (hv : ∀ k : ℤ, v (-k) = v k) (hw : ∀ k : ℤ, w (-k) = w k) :
    proposition59LatticeTrace L N
        (fun x => proposition59RealTransform L N v x *
          proposition59RealTransform L N w x) =
      2 * Real.pi * proposition59FullPairing N v w := by
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  have hzero : proposition59RealTransform L N v 0 * proposition59RealTransform L N w 0 =
      L * (v 0 * w 0) := by
    rw [proposition59RealTransform_at_zero hL, proposition59RealTransform_at_zero hL,
      proposition59Anchor, proposition59Anchor]
    calc Real.sqrt L * v 0 * (Real.sqrt L * w 0)
        = (Real.sqrt L * Real.sqrt L) * (v 0 * w 0) := by ring
      _ = L * (v 0 * w 0) := by rw [hsq]
  have hnode : ∀ n ∈ Finset.Icc 1 N,
      proposition59RealTransform L N v (proposition59RealPole L n) *
          proposition59RealTransform L N w (proposition59RealPole L n) =
        L * (v (n : ℤ) * w (n : ℤ)) := by
    intro n hn
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    rw [proposition59RealTransform_at_realPole hL N v hnN,
      proposition59RealTransform_at_realPole hL N w hnN]
    have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n, by ring⟩
    calc Real.sqrt L * (-1 : ℝ) ^ n * v (n : ℤ) *
          (Real.sqrt L * (-1 : ℝ) ^ n * w (n : ℤ))
        = (Real.sqrt L * Real.sqrt L) * ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
            (v (n : ℤ) * w (n : ℤ)) := by ring
      _ = L * (v (n : ℤ) * w (n : ℤ)) := by rw [hsq, hsign]; ring
  have hpair : proposition59FullPairing N v w =
      v 0 * w 0 + 2 * ∑ n ∈ Finset.Icc 1 N, v (n : ℤ) * w (n : ℤ) := by
    rw [proposition59FullPairing, sum_Icc_symm_split]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hv (n : ℤ), hw (n : ℤ)]
    ring
  simp only [proposition59LatticeTrace]
  rw [hzero, Finset.sum_congr rfl hnode, ← Finset.mul_sum, hpair]
  field_simp

/-! ## Item 2 — `P59_ANCHORED_EIGENBASIS_DECOMPOSITION` (verdict identities (A), (B))

Everything in this block is **linearity of the transform and of the anchor**.  No
orthonormality of the family `u` is used, and none is assumed: the eigenbasis enters
only through the expansion hypothesis `hy`. -/

/-- Linearity of the source raw transform in its coefficient row. -/
theorem proposition59RawTransform_of_sum
    (L : ℝ) (S : Finset ℤ) (T : Finset ℕ) (d : ℕ → ℂ) (u : ℕ → ℤ → ℂ) (z : ℂ) :
    proposition59RawTransform L S (fun k => ∑ j ∈ T, d j * u j k) z =
      ∑ j ∈ T, d j * proposition59RawTransform L S (u j) z := by
  have hswap : (∑ k ∈ S, (∑ j ∈ T, d j * u j k) * proposition59PoleKernel L k z) =
      ∑ j ∈ T, d j * ∑ k ∈ S, u j k * proposition59PoleKernel L k z := by
    have h1 : ∀ k : ℤ, (∑ j ∈ T, d j * u j k) * proposition59PoleKernel L k z =
        ∑ j ∈ T, d j * (u j k * proposition59PoleKernel L k z) := by
      intro k
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  unfold proposition59RawTransform
  rw [hswap, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Linearity of the real P59 transform in its real coefficient row. -/
theorem proposition59RealTransform_of_sum
    (L : ℝ) (N K : ℕ) (u : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (y : ℤ → ℝ)
    (hy : ∀ k : ℤ, y k = ∑ j ∈ Finset.Icc 1 K, d j * u j k) (x : ℝ) :
    proposition59RealTransform L N y x =
      ∑ j ∈ Finset.Icc 1 K, d j * proposition59RealTransform L N (u j) x := by
  unfold proposition59RealTransform
  have hrow : (fun k : ℤ => ((y k : ℝ) : ℂ)) =
      fun k : ℤ => ∑ j ∈ Finset.Icc 1 K, ((d j : ℝ) : ℂ) * ((u j k : ℝ) : ℂ) := by
    funext k
    rw [hy k]
    push_cast
    ring
  rw [hrow, proposition59RawTransform_of_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun j _ => Complex.re_ofReal_mul _ _

/-- Linearity of the anchor: `ℓ(y) = ∑_j d_j ℓ_j`.  This is the exact statement that the
extra `X`-term of the naive decomposition vanishes. -/
theorem proposition59Anchor_of_sum
    (L : ℝ) (K : ℕ) (u : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (y : ℤ → ℝ)
    (hy : ∀ k : ℤ, y k = ∑ j ∈ Finset.Icc 1 K, d j * u j k) :
    proposition59Anchor L y = ∑ j ∈ Finset.Icc 1 K, d j * proposition59Anchor L (u j) := by
  unfold proposition59Anchor
  rw [hy 0, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The verdict's anchored defect: `ψ_j = F_{u_j} − ℓ_j X` for a basis row, and
`e = F_y − ℓ(y) X` for the sample row `y`.  One definition covers both. -/
def proposition59AnchoredDefect (L : ℝ) (N : ℕ) (v : ℤ → ℝ) (X : ℝ → ℝ) : ℝ → ℝ :=
  fun x => proposition59RealTransform L N v x - proposition59Anchor L v * X x

/-- The residual `X`-term of the naive anchored decomposition is exactly zero — the
statement the task asks to be made explicit rather than silently dropped. -/
theorem proposition59_anchor_residual_term_zero
    (L : ℝ) (K : ℕ) (u : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (y : ℤ → ℝ) (hK : 1 ≤ K)
    (hy : ∀ k : ℤ, y k = ∑ j ∈ Finset.Icc 1 K, d j * u j k) :
    proposition59Anchor L y - d 1 * proposition59Anchor L (u 1)
        - ∑ j ∈ Finset.Icc 2 K, d j * proposition59Anchor L (u j) = 0 := by
  have hsplit : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 K := by
    simp only [Finset.mem_Icc, not_and, not_le]
    omega
  rw [proposition59Anchor_of_sum L K u d y hy, hsplit, Finset.sum_insert h1]
  ring

/-- `e = ∑_j d_j ψ_j`: the anchored defect is linear along the expansion. -/
theorem proposition59_anchoredDefect_of_sum
    (L : ℝ) (N K : ℕ) (u : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (y : ℤ → ℝ) (X : ℝ → ℝ)
    (hy : ∀ k : ℤ, y k = ∑ j ∈ Finset.Icc 1 K, d j * u j k) (x : ℝ) :
    proposition59AnchoredDefect L N y X x =
      ∑ j ∈ Finset.Icc 1 K, d j * proposition59AnchoredDefect L N (u j) X x := by
  unfold proposition59AnchoredDefect
  rw [proposition59RealTransform_of_sum L N K u d y hy x,
    proposition59Anchor_of_sum L K u d y hy, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Identity (A)**, `P59_ANCHORED_EIGENBASIS_DECOMPOSITION`:
`d₁ℓ₁(G − X) = e − ∑_{j≥2} d_j ψ_j`, with `G = F_{u₁}/ℓ₁`.

Orthonormality of `u` is **not** used; only the expansion `hy` and linearity. -/
theorem proposition59_anchored_eigenbasis_decomposition
    {L : ℝ} (N K : ℕ) (u : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (y : ℤ → ℝ) (X : ℝ → ℝ)
    (hK : 1 ≤ K) (hℓ : proposition59Anchor L (u 1) ≠ 0)
    (hy : ∀ k : ℤ, y k = ∑ j ∈ Finset.Icc 1 K, d j * u j k) (x : ℝ) :
    d 1 * proposition59Anchor L (u 1) *
        (proposition59RealTransform L N (u 1) x / proposition59Anchor L (u 1) - X x) =
      proposition59AnchoredDefect L N y X x -
        ∑ j ∈ Finset.Icc 2 K, d j * proposition59AnchoredDefect L N (u j) X x := by
  have hsplit : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 K := by
    simp only [Finset.mem_Icc, not_and, not_le]
    omega
  rw [proposition59_anchoredDefect_of_sum L N K u d y X hy x, hsplit,
    Finset.sum_insert h1]
  unfold proposition59AnchoredDefect
  field_simp
  ring

/-- **Identity (B)**, the two-mode form of (A): with `a = -d₂/(d₁ℓ₁)` and
`R = (e - ∑_{j≥3} d_j ψ_j)/(d₁ℓ₁)` one has `G - X = a ψ₂ + R`.  Both `a` and `R` are
*defined* by the identity; nothing is fitted. -/
theorem proposition59_anchored_two_mode_form
    {L : ℝ} (N K : ℕ) (u : ℕ → ℤ → ℝ) (d : ℕ → ℝ) (y : ℤ → ℝ) (X : ℝ → ℝ)
    (hK : 2 ≤ K) (hℓ : proposition59Anchor L (u 1) ≠ 0) (hd : d 1 ≠ 0)
    (hy : ∀ k : ℤ, y k = ∑ j ∈ Finset.Icc 1 K, d j * u j k) (x : ℝ) :
    proposition59RealTransform L N (u 1) x / proposition59Anchor L (u 1) - X x =
      (-(d 2) / (d 1 * proposition59Anchor L (u 1))) *
          proposition59AnchoredDefect L N (u 2) X x +
        (proposition59AnchoredDefect L N y X x -
            ∑ j ∈ Finset.Icc 3 K, d j * proposition59AnchoredDefect L N (u j) X x) /
          (d 1 * proposition59Anchor L (u 1)) := by
  have hA := proposition59_anchored_eigenbasis_decomposition (L := L) N K u d y X
    (le_trans (by omega) hK) hℓ hy x
  have hsplit : Finset.Icc 2 K = insert 2 (Finset.Icc 3 K) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h2 : (2 : ℕ) ∉ Finset.Icc 3 K := by
    simp only [Finset.mem_Icc, not_and, not_le]
    omega
  rw [hsplit, Finset.sum_insert h2] at hA
  have hne : d 1 * proposition59Anchor L (u 1) ≠ 0 := mul_ne_zero hd hℓ
  field_simp at hA ⊢
  linarith [hA]

/-! ## Item 3 — `P59_SECOND_MODE_OVERLAP_LATTICE_IDENTITY` (verdict identity (D))

The verdict's normalization repair `y[0] = u₁[0]`, hence `ℓ(y) = ℓ₁` and
`F_y(x_n) = ℓ₁ X(x_n)` at every included node. -/

/-- The verdict's normalized sample row of a profile `X`:
`y_k = (−1)^{|k|} u₁[0] X(2π|k|/L)`.  It is even by construction, and `y[0] = u₁[0]`
whenever `X 0 = 1`.  `X` is an arbitrary real profile — no property of `Ξ` is used. -/
def proposition59XiSampleRow (L : ℝ) (u₁ : ℤ → ℝ) (X : ℝ → ℝ) (k : ℤ) : ℝ :=
  (-1 : ℝ) ^ k.natAbs * u₁ 0 * X (proposition59RealPole L k.natAbs)

theorem proposition59XiSampleRow_even (L : ℝ) (u₁ : ℤ → ℝ) (X : ℝ → ℝ) (k : ℤ) :
    proposition59XiSampleRow L u₁ X (-k) = proposition59XiSampleRow L u₁ X k := by
  unfold proposition59XiSampleRow
  rw [Int.natAbs_neg]

/-- The verdict's normalization `y[0] = u₁[0]`. -/
theorem proposition59XiSampleRow_at_zero (L : ℝ) (u₁ : ℤ → ℝ) (X : ℝ → ℝ)
    (hX : X 0 = 1) :
    proposition59XiSampleRow L u₁ X 0 = u₁ 0 := by
  unfold proposition59XiSampleRow
  rw [show (0 : ℤ).natAbs = 0 from rfl, proposition59RealPole_zero, hX]
  ring

/-- The sample row's transform agrees with `ℓ₁ X` at every included node. -/
theorem proposition59RealTransform_xiSampleRow_at_realPole
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u₁ : ℤ → ℝ) (X : ℝ → ℝ) {n : ℕ} (hn : n ≤ N) :
    proposition59RealTransform L N (proposition59XiSampleRow L u₁ X)
        (proposition59RealPole L n) =
      proposition59Anchor L u₁ * X (proposition59RealPole L n) := by
  rw [proposition59RealTransform_at_realPole hL N _ hn]
  unfold proposition59XiSampleRow proposition59Anchor
  rw [show ((n : ℤ)).natAbs = n from Int.natAbs_natCast n]
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨n, by ring⟩
  calc Real.sqrt L * (-1 : ℝ) ^ n *
        ((-1 : ℝ) ^ n * u₁ 0 * X (proposition59RealPole L n))
      = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
          (Real.sqrt L * u₁ 0 * X (proposition59RealPole L n)) := by ring
    _ = Real.sqrt L * u₁ 0 * X (proposition59RealPole L n) := by rw [hsign]; ring

theorem proposition59RealTransform_xiSampleRow_at_zero
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u₁ : ℤ → ℝ) (X : ℝ → ℝ) :
    proposition59RealTransform L N (proposition59XiSampleRow L u₁ X) 0 =
      proposition59Anchor L u₁ * X 0 := by
  have h := proposition59RealTransform_xiSampleRow_at_realPole hL N u₁ X (Nat.zero_le N)
  rwa [proposition59RealPole_zero] at h

/-- **Identity (D)**, `P59_SECOND_MODE_OVERLAP_LATTICE_IDENTITY`:
`2π d₂ = ℓ₁ Tr_m(X F₂)`, where `d₂ = ⟨y, u₂⟩` is the exact second-mode overlap of the
normalized sample row.  Finite identity; no rate, no limit. -/
theorem proposition59_second_mode_overlap_lattice
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u₁ u₂ : ℤ → ℝ) (X : ℝ → ℝ)
    (h₂ : ∀ k : ℤ, u₂ (-k) = u₂ k) :
    2 * Real.pi * proposition59FullPairing N (proposition59XiSampleRow L u₁ X) u₂ =
      proposition59Anchor L u₁ *
        proposition59LatticeTrace L N
          (fun x => X x * proposition59RealTransform L N u₂ x) := by
  rw [← proposition59_real_even_lattice_pairing hL N _ u₂
    (proposition59XiSampleRow_even L u₁ X) h₂]
  rw [← proposition59LatticeTrace_const_mul]
  refine proposition59LatticeTrace_congr_nodes L N _ _ ?_ ?_
  · rw [proposition59RealTransform_xiSampleRow_at_zero hL]
    ring
  · intro n hn
    rw [proposition59RealTransform_xiSampleRow_at_realPole hL N u₁ X
      (Finset.mem_Icc.mp hn).2]
    ring

/-! ## Item 4 — `P59_SECOND_MODE_CURVATURE_TRANSFER_IDENTITY` (verdict identity (F)) -/

/-- The verdict's exact second-jet remainder function `B = G − X + α z² X`. -/
def proposition59JetRemainder (G X : ℝ → ℝ) (α : ℝ) : ℝ → ℝ :=
  fun x => G x - X x + α * x ^ 2 * X x

/-- The verdict's second-jet functional `κ(f) = −f''(0)/2`, written with `iteratedDeriv`
exactly as the P59 transform files do. -/
def proposition59Kappa (f : ℝ → ℝ) : ℝ := -(iteratedDeriv 2 f 0) / 2

/-- `B(0) = 0` whenever `G` and `X` share their anchor value. -/
theorem proposition59JetRemainder_at_zero (G X : ℝ → ℝ) (α : ℝ) (h : G 0 = X 0) :
    proposition59JetRemainder G X α 0 = 0 := by
  unfold proposition59JetRemainder
  rw [h]
  ring

/-- `d²/dx²(x² X)|₀ = 2 X(0)`: the one calculus fact behind the exact second jet of `B`. -/
private theorem iteratedDeriv_two_sq_mul (X : ℝ → ℝ) (hX : ContDiff ℝ 2 X) :
    iteratedDeriv 2 (fun x : ℝ => x ^ 2 * X x) 0 = 2 * X 0 := by
  have hsplit : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  have hXd : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hX' : ContDiff ℝ 1 (deriv X) := by
    rw [hsplit] at hX
    exact (contDiff_succ_iff_deriv.mp hX).2.2
  have hX'd : Differentiable ℝ (deriv X) := hX'.differentiable (le_refl 1)
  have hderiv : deriv (fun x : ℝ => x ^ 2 * X x) =
      fun x : ℝ => 2 * x * X x + x ^ 2 * deriv X x := by
    funext y
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    rw [show (fun x : ℝ => x ^ 2 * X x) = (fun x : ℝ => x ^ 2) * X from rfl,
      (h1.mul (hXd y).hasDerivAt).deriv]
  have hsucc : iteratedDeriv 2 (fun x : ℝ => x ^ 2 * X x) 0 =
      deriv (deriv (fun x : ℝ => x ^ 2 * X x)) 0 := by
    simp [iteratedDeriv_succ]
  have hA : HasDerivAt (fun x : ℝ => 2 * x * X x) (2 * X 0) 0 := by
    have h1 : HasDerivAt (fun x : ℝ => 2 * x) (2 : ℝ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    simpa using h1.mul (hXd 0).hasDerivAt
  have hB : HasDerivAt (fun x : ℝ => x ^ 2 * deriv X x) (0 : ℝ) 0 := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (0 : ℝ) 0 := by
      simpa using hasDerivAt_pow 2 (0 : ℝ)
    simpa using h1.mul (hX'd 0).hasDerivAt
  rw [hsucc, hderiv,
    show (fun x : ℝ => 2 * x * X x + x ^ 2 * deriv X x) =
      ((fun x : ℝ => 2 * x * X x) + fun x : ℝ => x ^ 2 * deriv X x) from rfl,
    (hA.add hB).deriv]
  ring

/-- `B''(0) = 0` for the verdict's **exact** second jet `α = κ(G) − κ(X)`: together with
`proposition59JetRemainder_at_zero` this is the verdict's `jets: [B(0)=0, B''(0)=0]`, i.e.
the fail-closed statement that `α` is the exact second jet and not a fitted coefficient. -/
theorem proposition59JetRemainder_secondJet_zero
    (G X : ℝ → ℝ) (hG : ContDiff ℝ 2 G) (hX : ContDiff ℝ 2 X) (hX0 : X 0 = 1) :
    proposition59Kappa
        (proposition59JetRemainder G X (proposition59Kappa G - proposition59Kappa X)) = 0 := by
  have hsq : ContDiffAt ℝ 2 (fun x : ℝ => x ^ 2 * X x) 0 :=
    (((contDiff_id (𝕜 := ℝ) (n := 2)).pow 2).mul hX).contDiffAt
  have hgen : ∀ a : ℝ, iteratedDeriv 2 (proposition59JetRemainder G X a) 0 =
      (iteratedDeriv 2 G 0 - iteratedDeriv 2 X 0) + a * (2 * X 0) := by
    intro a
    have hfun : proposition59JetRemainder G X a =
        (fun x : ℝ => G x - X x) + fun x : ℝ => a * (x ^ 2 * X x) := by
      funext x
      simp only [proposition59JetRemainder, Pi.add_apply]
      ring
    have hsubcd : ContDiffAt ℝ 2 (fun x : ℝ => G x - X x) 0 :=
      hG.contDiffAt.sub hX.contDiffAt
    have hmulcd : ContDiffAt ℝ 2 (fun x : ℝ => a * (x ^ 2 * X x)) 0 :=
      contDiffAt_const.mul hsq
    rw [hfun, iteratedDeriv_add hsubcd hmulcd]
    congr 1
    · have h := iteratedDeriv_sub (n := 2) (f := G) (g := X) (x := (0 : ℝ))
        hG.contDiffAt hX.contDiffAt
      simpa [Pi.sub_def] using h
    · rw [iteratedDeriv_const_mul hsq a, iteratedDeriv_two_sq_mul X hX]
  simp only [proposition59Kappa, hgen, hX0]
  ring

/-- The pure `Tr`-linearity half of the transfer identity:
`Tr(X F₂) = α Tr(z²X F₂) − Tr(B F₂) + Tr(G F₂)`.  No orthogonality, no P59 sampling. -/
theorem proposition59_curvature_transfer_split
    (L : ℝ) (N : ℕ) (G X F₂ : ℝ → ℝ) (α : ℝ) :
    proposition59LatticeTrace L N (fun x => X x * F₂ x) =
      α * proposition59LatticeTrace L N (fun x => x ^ 2 * X x * F₂ x)
        - proposition59LatticeTrace L N
            (fun x => proposition59JetRemainder G X α x * F₂ x)
        + proposition59LatticeTrace L N (fun x => G x * F₂ x) := by
  have key : ∀ x : ℝ, X x * F₂ x =
      α * (x ^ 2 * X x * F₂ x) - (proposition59JetRemainder G X α x * F₂ x) +
        G x * F₂ x := by
    intro x
    unfold proposition59JetRemainder
    ring
  simp only [proposition59LatticeTrace]
  rw [Finset.sum_congr rfl (fun n _ => key (proposition59RealPole L n)), key 0,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **Identity (E)**: the ground transform is `Tr`-orthogonal to the second mode
whenever the two rows are orthogonal — `Tr(G F₂) = 2π⟨u₁,u₂⟩/ℓ₁ = 0`. -/
theorem proposition59_ground_second_mode_trace_orthogonality
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u₁ u₂ : ℤ → ℝ)
    (h₁ : ∀ k : ℤ, u₁ (-k) = u₁ k) (h₂ : ∀ k : ℤ, u₂ (-k) = u₂ k)
    (hℓ : proposition59Anchor L u₁ ≠ 0)
    (horth : proposition59FullPairing N u₁ u₂ = 0) :
    proposition59LatticeTrace L N
        (fun x => proposition59RealTransform L N u₁ x / proposition59Anchor L u₁ *
          proposition59RealTransform L N u₂ x) = 0 := by
  have hrewrite : (fun x : ℝ =>
      proposition59RealTransform L N u₁ x / proposition59Anchor L u₁ *
        proposition59RealTransform L N u₂ x) =
      fun x : ℝ => (proposition59Anchor L u₁)⁻¹ *
        (proposition59RealTransform L N u₁ x * proposition59RealTransform L N u₂ x) := by
    funext x
    field_simp
  rw [hrewrite, proposition59LatticeTrace_const_mul,
    proposition59_real_even_lattice_pairing hL N u₁ u₂ h₁ h₂, horth]
  ring

/-- **Identity (F)**, `P59_SECOND_MODE_CURVATURE_TRANSFER_IDENTITY`:
`2π d₂ = ℓ₁ (α M − E)` with `M = Tr(z² X F₂)` and `E = Tr(B F₂)`.

`α` is an arbitrary real parameter here — the identity holds for every `α`, and in
particular for the verdict's exact second jet `α = κ(G) − κ(X)`, which item 5 supplies.
No rate is claimed for `M` or `E`. -/
theorem proposition59_second_mode_curvature_transfer
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u₁ u₂ : ℤ → ℝ) (X : ℝ → ℝ) (α : ℝ)
    (h₁ : ∀ k : ℤ, u₁ (-k) = u₁ k) (h₂ : ∀ k : ℤ, u₂ (-k) = u₂ k)
    (hℓ : proposition59Anchor L u₁ ≠ 0)
    (horth : proposition59FullPairing N u₁ u₂ = 0) :
    2 * Real.pi * proposition59FullPairing N (proposition59XiSampleRow L u₁ X) u₂ =
      proposition59Anchor L u₁ *
        (α * proposition59LatticeTrace L N
              (fun x => x ^ 2 * X x * proposition59RealTransform L N u₂ x)
          - proposition59LatticeTrace L N
              (fun x => proposition59JetRemainder
                  (fun t => proposition59RealTransform L N u₁ t /
                    proposition59Anchor L u₁) X α x *
                proposition59RealTransform L N u₂ x)) := by
  rw [proposition59_second_mode_overlap_lattice hL N u₁ u₂ X h₂,
    proposition59_curvature_transfer_split L N
      (fun t => proposition59RealTransform L N u₁ t / proposition59Anchor L u₁) X
      (proposition59RealTransform L N u₂) α,
    proposition59_ground_second_mode_trace_orthogonality hL N u₁ u₂ h₁ h₂ hℓ horth]
  ring

/-! ## Item 5 — `P59_SECOND_JET_TWO_MODE_LEDGER` (verdict identity (G)) -/

/-- **Identity (G)**, `P59_SECOND_JET_TWO_MODE_LEDGER`:
from the two-mode form `G − X = a ψ₂ + R` (identity (B), where `a` and `R` are defined
by that identity) the second jets add:
`α := κ(G) − κ(X) = a κ(ψ₂) + κ(R)`.

Pure linearity of `iteratedDeriv`; the `C²` hypotheses are the ones Mathlib's
`iteratedDeriv_sub` / `iteratedDeriv_add` / `iteratedDeriv_const_mul` require. -/
theorem proposition59_second_jet_two_mode_ledger
    (G X ψ R : ℝ → ℝ) (a : ℝ)
    (hG : ContDiffAt ℝ 2 G 0) (hX : ContDiffAt ℝ 2 X 0)
    (hψ : ContDiffAt ℝ 2 ψ 0) (hR : ContDiffAt ℝ 2 R 0)
    (hdecomp : (fun x => G x - X x) = fun x => a * ψ x + R x) :
    proposition59Kappa G - proposition59Kappa X =
      a * proposition59Kappa ψ + proposition59Kappa R := by
  have hsub : iteratedDeriv 2 (fun x => G x - X x) 0 =
      iteratedDeriv 2 G 0 - iteratedDeriv 2 X 0 := by
    have := iteratedDeriv_sub (n := 2) (f := G) (g := X) (x := (0 : ℝ)) hG hX
    simpa [Pi.sub_def] using this
  have hadd : iteratedDeriv 2 (fun x => a * ψ x + R x) 0 =
      a * iteratedDeriv 2 ψ 0 + iteratedDeriv 2 R 0 := by
    have hmul : ContDiffAt ℝ 2 (fun x => a * ψ x) 0 := contDiffAt_const.mul hψ
    have h := iteratedDeriv_add (n := 2) (f := fun x => a * ψ x) (g := R)
      (x := (0 : ℝ)) hmul hR
    rw [show ((fun x => a * ψ x) + R) = (fun x => a * ψ x + R x) from rfl] at h
    rw [h, iteratedDeriv_const_mul hψ a]
  have hkey : iteratedDeriv 2 G 0 - iteratedDeriv 2 X 0 =
      a * iteratedDeriv 2 ψ 0 + iteratedDeriv 2 R 0 := by
    rw [← hsub, hdecomp, hadd]
  unfold proposition59Kappa
  linarith [hkey]

#print axioms proposition59_even_coords_pairing
#print axioms proposition59RealTransform_at_realPole
#print axioms proposition59RealTransform_at_zero
#print axioms proposition59_real_even_lattice_pairing
#print axioms proposition59RawTransform_of_sum
#print axioms proposition59RealTransform_of_sum
#print axioms proposition59Anchor_of_sum
#print axioms proposition59_anchor_residual_term_zero
#print axioms proposition59_anchoredDefect_of_sum
#print axioms proposition59_anchored_eigenbasis_decomposition
#print axioms proposition59_anchored_two_mode_form
#print axioms proposition59XiSampleRow_at_zero
#print axioms proposition59RealTransform_xiSampleRow_at_realPole
#print axioms proposition59_second_mode_overlap_lattice
#print axioms proposition59JetRemainder_at_zero
#print axioms proposition59JetRemainder_secondJet_zero
#print axioms proposition59_curvature_transfer_split
#print axioms proposition59_ground_second_mode_trace_orthogonality
#print axioms proposition59_second_mode_curvature_transfer
#print axioms proposition59_second_jet_two_mode_ledger

end Q3.RouteB
