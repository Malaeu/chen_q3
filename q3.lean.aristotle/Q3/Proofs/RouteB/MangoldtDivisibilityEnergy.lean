import Mathlib

/-!
# Λ-divisibility energy identity (judge's `mangoldt_divisibility_energy_identity`)

Lean-ready head 1 of `docs/routeB_bus/proshka/`
`PROSHKA_VERDICT_WEILPROOF_CONTINUATION_ARITHMETIC_PACKETS_AND_DENSITY_2026-09-05.md`
(§3 Lemma 2 = `(DIV)`, §4 Lemma 3 = `(B)`/`(PRIME)`, names fixed in §11).

Everything here is **finite arithmetic over `ℂ`**: divisibility and the literal von
Mangoldt weights.  No zeta zeros, no Weil form, no positivity of `Q` is assumed, used
or claimed, and nothing in this file is conditional on RH.

## Statement

For `M : ℕ` and `c : ℕ → ℂ` put

* `divPairs M = {(n, d) : n ≥ 1, d ≥ 2, n * d ≤ M}`,
* `B M n = ∑_{d ≥ 2, n d ≤ M} Λ d / d`   (the verdict's `B(M/n)`),
* `diagWeight M n = log n + B M n`       (the verdict's `a_n^{(M)}`),
* `primeForm M c = 2 Re ∑_{(n,d) ∈ divPairs M} Λ d / √d · conj (c n) · c (n d)`,
* `energy M c = ∑_{(n,d) ∈ divPairs M} Λ d · ‖c (n d) − c n / √d‖²`.

`mangoldt_divisibility_energy_identity`:

  `(∑_{n = 1}^{M} a_n |c_n|²) − P_M(c) = ∑_{n ≥ 1, d ≥ 2, n d ≤ M} Λ d |c_{nd} − c_n/√d|²`

The verdict states it for `M ≥ 2`; the hypothesis is not needed — both sides are `0`
for `M ≤ 1` — so the theorem is proved for every `M`.

## Proof (the verdict's, verbatim)

Expand the square termwise (`norm_sub_div_ofReal_sq`).  The `|c_n|²` term collects
into `B M n` (`sum_divPairs_curry`).  The `|c_{nd}|²` term is re-indexed by `j = n d`
(`sum_divPairs_reindex`) and uses `∑_{d ∣ j} Λ d = log j`
(`ArithmeticFunction.vonMangoldt_sum`); `d = 1` drops out because `Λ 1 = 0`
(`sum_vonMangoldt_ge_two`).  The mixed term is `−P_M(c)`.

## Corollaries

* `energy_nonneg` — (i), the right-hand side is `≥ 0`;
* `plant_energy_zero`, `plant_identity_zero`, `plant_doubled_edge_eq`,
  `plant_doubled_edge_neg` — (ii), the verdict's calibration plant `M = 2`,
  `c = (1, 1/√2)`: the right-hand side vanishes, and with the prime edge illegally
  doubled the left-hand side equals `−log 2 < 0`.  A checker that only tests
  Hermitian symmetry therefore does not certify the identity;
* `primeForm_le_diag`, `primeForm_le_max` — (iii) in diagonal and uniform form;
* `B_one_le`, `diagWeight_le`, `primeForm_le_log` — the verdict's `(B)`/`(PRIME)`
  with Mathlib's Chebyshev constant: `B(N) ≤ log N + (log 4 + 4)` and
  `P_M(c) ≤ (log M + (log 4 + 4)) ‖c‖²`.  The verdict's sharper `4 log 2` needs its
  own central-binomial run of `ψ`; Mathlib supplies `Chebyshev.psi_le_const_mul_self`
  with `(log 4 + 4)`, so that constant is what is proved here.  The step
  `∑_{j ≤ N} log j = ∑_{d ≤ N} Λ d ⌊N/d⌋` is not in Mathlib and is proved here
  (`sum_log_eq_sum_floor`) from the same divisor re-indexing.

Nothing in this file depends on any other Q3 module.
-/

open Finset ArithmeticFunction

namespace Q3
namespace RouteB
namespace MangoldtDivisibilityEnergy

noncomputable section

/-- Pairs `(n, d)` with `n ≥ 1`, `d ≥ 2` and `n * d ≤ M`. -/
def divPairs (M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 M ×ˢ Finset.Icc 2 M).filter fun p => p.1 * p.2 ≤ M

/-- Pairs `(j, d)` with `1 ≤ j ≤ M`, `d ≥ 2` and `d ∣ j`. -/
def divisorPairs (M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 M ×ˢ Finset.Icc 2 M).filter fun p => p.2 ∣ p.1

lemma mem_divPairs {M : ℕ} {p : ℕ × ℕ} :
    p ∈ divPairs M ↔ 1 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 * p.2 ≤ M := by
  constructor
  · intro h
    simp only [divPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
    exact ⟨h.1.1.1, h.1.2.1, h.2⟩
  · rintro ⟨h1, h2, h3⟩
    have hd1 : 1 ≤ p.2 := le_trans one_le_two h2
    have hn : p.1 ≤ p.1 * p.2 := by
      calc p.1 = p.1 * 1 := (mul_one _).symm
        _ ≤ p.1 * p.2 := Nat.mul_le_mul (le_refl _) hd1
    have hd : p.2 ≤ p.1 * p.2 := by
      calc p.2 = 1 * p.2 := (one_mul _).symm
        _ ≤ p.1 * p.2 := Nat.mul_le_mul h1 (le_refl _)
    simp only [divPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨h1, le_trans hn h3⟩, ⟨h2, le_trans hd h3⟩⟩, h3⟩

lemma mem_divisorPairs {M : ℕ} {p : ℕ × ℕ} :
    p ∈ divisorPairs M ↔ 1 ≤ p.1 ∧ p.1 ≤ M ∧ 2 ≤ p.2 ∧ p.2 ∣ p.1 := by
  constructor
  · intro h
    simp only [divisorPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2.1, h.2⟩
  · rintro ⟨h1, h1M, h2, hdvd⟩
    have hdle : p.2 ≤ p.1 := Nat.le_of_dvd (by omega) hdvd
    simp only [divisorPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨h1, h1M⟩, ⟨h2, le_trans hdle h1M⟩⟩, hdvd⟩

/-- `B M n = ∑_{d ≥ 2, n d ≤ M} Λ(d)/d`, i.e. the judge's `B(M/n)`. -/
def B (M n : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 2 M).filter fun d => n * d ≤ M, vonMangoldt d / d

/-- Diagonal weight `a_n^{(M)} = log n + B(M/n)`. -/
def diagWeight (M n : ℕ) : ℝ := Real.log n + B M n

/-- `P_M(c) = 2 Re ∑_{n ≥ 1, d ≥ 2, n d ≤ M} Λ(d)/√d · conj(c_n) c_{nd}`. -/
def primeForm (M : ℕ) (c : ℕ → ℂ) : ℝ :=
  2 * (∑ p ∈ divPairs M,
      ((vonMangoldt p.2 : ℝ) : ℂ) / ((Real.sqrt p.2 : ℝ) : ℂ) *
        (starRingEnd ℂ) (c p.1) * c (p.1 * p.2)).re

/-- `∑_{n ≥ 1, d ≥ 2, n d ≤ M} Λ(d) |c_{nd} − c_n/√d|²`. -/
def energy (M : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ p ∈ divPairs M, vonMangoldt p.2 * ‖c (p.1 * p.2) - c p.1 / ((Real.sqrt p.2 : ℝ) : ℂ)‖ ^ 2

lemma norm_sub_div_ofReal_sq (A z : ℂ) (s : ℝ) (hs : s ≠ 0) :
    ‖A - z / (s : ℂ)‖ ^ 2
      = ‖A‖ ^ 2 + ‖z‖ ^ 2 / s ^ 2 - 2 * (((starRingEnd ℂ) z * A).re) / s := by
  have h : ∀ w : ℂ, ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    intro w; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [h, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  field_simp
  ring

lemma sum_divPairs_curry (M : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ divPairs M, f p.1 p.2
      = ∑ n ∈ Finset.Icc 1 M, ∑ d ∈ (Finset.Icc 2 M).filter (fun d => n * d ≤ M), f n d := by
  refine Finset.sum_finset_product' _ _ _ ?_
  intro p
  simp only [divPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

lemma sum_divisorPairs_curry (M : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ divisorPairs M, f p.1 p.2
      = ∑ j ∈ Finset.Icc 1 M, ∑ d ∈ (Finset.Icc 2 M).filter (fun d => d ∣ j), f j d := by
  refine Finset.sum_finset_product' _ _ _ ?_
  intro p
  simp only [divisorPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

lemma sum_divPairs_reindex (M : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p ∈ divPairs M, g (p.1 * p.2) p.2 = ∑ p ∈ divisorPairs M, g p.1 p.2 := by
  refine Finset.sum_nbij' (fun p => (p.1 * p.2, p.2)) (fun p => (p.1 / p.2, p.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_divPairs.mp hp
    refine mem_divisorPairs.mpr ⟨?_, h3, h2, ⟨p.1, mul_comm _ _⟩⟩
    have : 1 * 1 ≤ p.1 * p.2 := Nat.mul_le_mul h1 (by omega)
    simpa using this
  · intro p hp
    obtain ⟨h1, h1M, h2, hdvd⟩ := mem_divisorPairs.mp hp
    have hq : p.1 / p.2 * p.2 = p.1 := Nat.div_mul_cancel hdvd
    refine mem_divPairs.mpr ⟨?_, h2, ?_⟩
    · rcases Nat.eq_zero_or_pos (p.1 / p.2) with h | h
      · rw [h, zero_mul] at hq; omega
      · exact h
    · rw [hq]; exact h1M
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_divPairs.mp hp
    have : p.1 * p.2 / p.2 = p.1 := Nat.mul_div_cancel _ (by omega)
    simp [this]
  · intro p hp
    obtain ⟨h1, h1M, h2, hdvd⟩ := mem_divisorPairs.mp hp
    have : p.1 / p.2 * p.2 = p.1 := Nat.div_mul_cancel hdvd
    simp [this]
  · intro p _; rfl

lemma sum_vonMangoldt_ge_two (M j : ℕ) (hj : 1 ≤ j) (hjM : j ≤ M) :
    ∑ d ∈ (Finset.Icc 2 M).filter (fun d => d ∣ j), vonMangoldt d = Real.log j := by
  rw [← vonMangoldt_sum (n := j)]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
  · intro d hd hnot
    rw [Nat.mem_divisors] at hd
    have hdle : d ≤ j := Nat.le_of_dvd (by omega) hd.1
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hd.2 (Nat.eq_zero_of_zero_dvd hd.1)
    simp only [Finset.mem_filter, Finset.mem_Icc, not_and] at hnot
    have : d = 1 := by
      by_contra hne
      exact absurd hd.1 (by
        have h2 : 2 ≤ d := by omega
        exact fun _ => (hnot ⟨h2, by omega⟩) hd.1)
    rw [this, vonMangoldt_apply_one]

/-- **(DIV)** the judge's `mangoldt_divisibility_energy_identity`. -/
theorem mangoldt_divisibility_energy_identity (M : ℕ) (c : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 M, diagWeight M n * ‖c n‖ ^ 2) - primeForm M c = energy M c := by
  -- termwise expansion of the energy
  have hE : energy M c = ∑ p ∈ divPairs M,
      (vonMangoldt p.2 * ‖c (p.1 * p.2)‖ ^ 2
        + vonMangoldt p.2 / p.2 * ‖c p.1‖ ^ 2
        - 2 * (vonMangoldt p.2 / Real.sqrt p.2 *
            ((starRingEnd ℂ) (c p.1) * c (p.1 * p.2)).re)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2, h3⟩ := mem_divPairs.mp hp
    have hd0 : (0 : ℝ) < (p.2 : ℝ) := by
      have : (2 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast h2
      linarith
    have hs0 : (0 : ℝ) < Real.sqrt p.2 := Real.sqrt_pos.mpr hd0
    have hsq : Real.sqrt (p.2 : ℝ) ^ 2 = (p.2 : ℝ) := Real.sq_sqrt hd0.le
    rw [norm_sub_div_ofReal_sq _ _ _ (ne_of_gt hs0), hsq]
    ring
  have hP : primeForm M c = ∑ p ∈ divPairs M,
      2 * (vonMangoldt p.2 / Real.sqrt p.2 *
        ((starRingEnd ℂ) (c p.1) * c (p.1 * p.2)).re) := by
    rw [primeForm, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_assoc, ← Complex.ofReal_div, Complex.re_ofReal_mul]
  have hDiag : ∑ p ∈ divPairs M, vonMangoldt p.2 / (p.2 : ℝ) * ‖c p.1‖ ^ 2
      = ∑ n ∈ Finset.Icc 1 M, B M n * ‖c n‖ ^ 2 := by
    rw [sum_divPairs_curry M (fun n d => vonMangoldt d / (d : ℝ) * ‖c n‖ ^ 2)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [B, Finset.sum_mul]
  have hLog : ∑ p ∈ divPairs M, vonMangoldt p.2 * ‖c (p.1 * p.2)‖ ^ 2
      = ∑ j ∈ Finset.Icc 1 M, Real.log j * ‖c j‖ ^ 2 := by
    rw [sum_divPairs_reindex M (fun j d => vonMangoldt d * ‖c j‖ ^ 2),
      sum_divisorPairs_curry M (fun j d => vonMangoldt d * ‖c j‖ ^ 2)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rw [← Finset.sum_mul, sum_vonMangoldt_ge_two M j hj.1 hj.2]
  rw [hE, Finset.sum_sub_distrib, Finset.sum_add_distrib, hLog, hDiag, ← hP,
    ← Finset.sum_add_distrib]
  refine congrArg (fun x => x - primeForm M c) (Finset.sum_congr rfl fun n _ => ?_)
  rw [diagWeight, add_mul]

/-- (i) the right-hand side of (DIV) is nonnegative. -/
theorem energy_nonneg (M : ℕ) (c : ℕ → ℂ) : 0 ≤ energy M c :=
  Finset.sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg (sq_nonneg _)

/-- (iii) (PRIME, diagonal form). -/
theorem primeForm_le_diag (M : ℕ) (c : ℕ → ℂ) :
    primeForm M c ≤ ∑ n ∈ Finset.Icc 1 M, diagWeight M n * ‖c n‖ ^ 2 := by
  have h := mangoldt_divisibility_energy_identity M c
  have h0 := energy_nonneg M c
  linarith

/-- (iii') uniform version. -/
theorem primeForm_le_max (M : ℕ) (c : ℕ → ℂ) (A : ℝ)
    (hA : ∀ n ∈ Finset.Icc 1 M, diagWeight M n ≤ A) :
    primeForm M c ≤ A * ∑ n ∈ Finset.Icc 1 M, ‖c n‖ ^ 2 := by
  refine le_trans (primeForm_le_diag M c) ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun n hn => by
    exact mul_le_mul_of_nonneg_right (hA n hn) (sq_nonneg _)

/-! ## Calibration plant (`M = 2`, `c = (1, 1/√2)`) -/

/-- The plant vector `c = (1, 1/√2)`. -/
def plantVec : ℕ → ℂ := fun n => if n = 1 then 1 else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma divPairs_two : divPairs 2 = {(1, 2)} := by
  ext p
  simp only [mem_divPairs, Finset.mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hn : p.1 = 1 := by
      by_contra h
      have h2' : 2 ≤ p.1 := by omega
      have : 2 * 2 ≤ p.1 * p.2 := Nat.mul_le_mul h2' h2
      omega
    refine ⟨hn, ?_⟩
    rw [hn, one_mul] at h3
    omega
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    norm_num

lemma plant_energy_zero : energy 2 plantVec = 0 := by
  rw [energy, divPairs_two, Finset.sum_singleton]
  norm_num [plantVec]

lemma plant_primeForm : primeForm 2 plantVec = Real.log 2 := by
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hL : vonMangoldt 2 = Real.log 2 := by
    simpa using vonMangoldt_apply_prime Nat.prime_two
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt hpos
  have hre : (Complex.log 2).re = Real.log 2 := by
    rw [Complex.log_re]
    norm_num
  rw [primeForm, divPairs_two, Finset.sum_singleton]
  norm_num [plantVec, hL]
  rw [hre]
  field_simp

theorem plant_identity_zero :
    (∑ n ∈ Finset.Icc 1 2, diagWeight 2 n * ‖plantVec n‖ ^ 2) - primeForm 2 plantVec = 0 := by
  rw [mangoldt_divisibility_energy_identity, plant_energy_zero]

theorem plant_doubled_edge_eq :
    (∑ n ∈ Finset.Icc 1 2, diagWeight 2 n * ‖plantVec n‖ ^ 2) - 2 * primeForm 2 plantVec
      = -Real.log 2 := by
  have h := plant_identity_zero
  have hp := plant_primeForm
  linarith

theorem plant_doubled_edge_neg :
    (∑ n ∈ Finset.Icc 1 2, diagWeight 2 n * ‖plantVec n‖ ^ 2) - 2 * primeForm 2 plantVec < 0 := by
  rw [plant_doubled_edge_eq]
  exact neg_lt_zero.mpr (Real.log_pos (by norm_num))

/-! ## A Chebyshev-type cap for `B` (Lemma 3, with Mathlib's constant) -/

lemma sum_divisorPairs_swap (N : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ divisorPairs N, f p.1 p.2
      = ∑ d ∈ Finset.Icc 2 N, ∑ j ∈ (Finset.Icc 1 N).filter (fun j => d ∣ j), f j d := by
  refine Finset.sum_finset_product_right' _ _ _ ?_
  intro p
  simp only [divisorPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

lemma card_multiples (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun j => d ∣ j)).card = N / d := by
  have h : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h]
  exact Nat.Ioc_filter_dvd_card_eq_div N d

lemma sum_log_eq_sum_floor (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, Real.log j
      = ∑ d ∈ Finset.Icc 2 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  have h1 : ∑ p ∈ divisorPairs N, vonMangoldt p.2 = ∑ j ∈ Finset.Icc 1 N, Real.log j := by
    rw [sum_divisorPairs_curry N (fun _ d => vonMangoldt d)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    exact sum_vonMangoldt_ge_two N j hj.1 hj.2
  have h2 : ∑ p ∈ divisorPairs N, vonMangoldt p.2
      = ∑ d ∈ Finset.Icc 2 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by
    rw [sum_divisorPairs_swap N (fun _ d => vonMangoldt d)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_multiples]
    ring
  rw [← h1, h2]

lemma B_one_eq (N : ℕ) : B N 1 = ∑ d ∈ Finset.Icc 2 N, vonMangoldt d / d := by
  rw [B]
  congr 1
  refine Finset.filter_true_of_mem fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  simpa using hd.2

lemma psi_natCast (N : ℕ) : Chebyshev.psi N = ∑ d ∈ Finset.Icc 2 N, vonMangoldt d := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    rw [Finset.mem_Icc] at hd
    rw [Finset.mem_Ioc]
    omega
  · intro d hd hnot
    rw [Finset.mem_Ioc] at hd
    simp only [Finset.mem_Icc, not_and, not_le] at hnot
    have hd1 : d = 1 := by
      by_contra hne
      have h2 : 2 ≤ d := by omega
      have := hnot h2
      omega
    rw [hd1, vonMangoldt_apply_one]

/-- Lemma 3 in the judge's numbering, with Mathlib's Chebyshev constant
`log 4 + 4` in place of `4 log 2`. -/
lemma B_one_le (N : ℕ) (hN : 1 ≤ N) :
    B N 1 ≤ Real.log N + (Real.log 4 + 4) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (N : ℝ) * B N 1
      ≤ ∑ d ∈ Finset.Icc 2 N, vonMangoldt d * (((N / d : ℕ) : ℝ) + 1) := by
    rw [B_one_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by
      have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
      linarith
    have hfloor : (N : ℝ) / d ≤ ((N / d : ℕ) : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one ((N : ℝ) / (d : ℕ))
      rw [Nat.floor_div_natCast, Nat.floor_natCast] at h
      exact le_of_lt h
    calc (N : ℝ) * (vonMangoldt d / d) = vonMangoldt d * ((N : ℝ) / d) := by ring
      _ ≤ vonMangoldt d * (((N / d : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hfloor vonMangoldt_nonneg
  have hsplit : ∑ d ∈ Finset.Icc 2 N, vonMangoldt d * (((N / d : ℕ) : ℝ) + 1)
      = (∑ d ∈ Finset.Icc 2 N, vonMangoldt d * ((N / d : ℕ) : ℝ))
        + ∑ d ∈ Finset.Icc 2 N, vonMangoldt d := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hlogsum : ∑ j ∈ Finset.Icc 1 N, Real.log j ≤ (N : ℝ) * Real.log N := by
    calc ∑ j ∈ Finset.Icc 1 N, Real.log j ≤ ∑ _j ∈ Finset.Icc 1 N, Real.log N := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_Icc] at hj
          have hj0 : (0 : ℝ) < j := by exact_mod_cast hj.1
          exact Real.log_le_log hj0 (by exact_mod_cast hj.2)
      _ = (N : ℝ) * Real.log N := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          norm_num
  have hpsi : ∑ d ∈ Finset.Icc 2 N, vonMangoldt d ≤ (Real.log 4 + 4) * N := by
    rw [← psi_natCast N]
    exact Chebyshev.psi_le_const_mul_self (by positivity)
  have hchain : (N : ℝ) * B N 1 ≤ (N : ℝ) * (Real.log N + (Real.log 4 + 4)) := by
    rw [hsplit, ← sum_log_eq_sum_floor] at key
    nlinarith [key, hlogsum, hpsi]
  exact le_of_mul_le_mul_left hchain hNpos

lemma B_eq_div (M n : ℕ) (hn : 1 ≤ n) : B M n = B (M / n) 1 := by
  rw [B, B]
  refine Finset.sum_congr ?_ fun d _ => rfl
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, one_mul]
  constructor
  · rintro ⟨⟨h2, _⟩, hnd⟩
    have hdq : d ≤ M / n := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hnd)
    exact ⟨⟨h2, hdq⟩, hdq⟩
  · rintro ⟨⟨h2, hdq⟩, _⟩
    have hdn : d * n ≤ M := (Nat.le_div_iff_mul_le (by omega)).mp hdq
    have hdM : d ≤ M := le_trans (Nat.le_mul_of_pos_right d (by omega)) hdn
    exact ⟨⟨h2, hdM⟩, by rw [mul_comm]; exact hdn⟩

lemma diagWeight_le (M n : ℕ) (hn : 1 ≤ n) (hnM : n ≤ M) :
    diagWeight M n ≤ Real.log M + (Real.log 4 + 4) := by
  have hq : 1 ≤ M / n := (Nat.one_le_div_iff (by omega)).mpr hnM
  have hB := B_one_le (M / n) hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < ((M / n : ℕ) : ℝ) := by exact_mod_cast hq
  have hlog : Real.log n + Real.log ((M / n : ℕ) : ℝ) ≤ Real.log M := by
    rw [← Real.log_mul (ne_of_gt hn0) (ne_of_gt hq0)]
    refine Real.log_le_log (by positivity) ?_
    have hnat : n * (M / n) ≤ M := by
      calc n * (M / n) = M / n * n := by rw [mul_comm]
        _ ≤ M := Nat.div_mul_le_self M n
    exact_mod_cast hnat
  rw [diagWeight, B_eq_div M n hn]
  linarith

/-- **(PRIME)** the explicit logarithmic cap on the prime operator. -/
theorem primeForm_le_log (M : ℕ) (c : ℕ → ℂ) :
    primeForm M c ≤ (Real.log M + (Real.log 4 + 4)) * ∑ n ∈ Finset.Icc 1 M, ‖c n‖ ^ 2 := by
  refine primeForm_le_max M c _ fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  exact diagWeight_le M n hn.1 hn.2

end

end MangoldtDivisibilityEnergy
end RouteB
end Q3
