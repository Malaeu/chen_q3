import Mathlib
import Q3.Proofs.PrimeCert.IntervalPilot
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFull
set_option maxHeartbeats 0

/-!
Scaffold for bucket-0 prime-power interval bounds.

We package the per-`n` numeric evidence needed to bound the envelope by a
rational constant. This file is intentionally lightweight and **not** in the
main chain.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

structure PrimeHeatEnvelopeBounds (n : ℕ) : Type where
  l : ℝ
  u : ℝ
  r : ℝ
  exp_ub : ℝ
  pi_lb : ℝ
  hl0 : 0 ≤ l
  hu0 : 0 ≤ u
  hlog_l : l ≤ Real.log (n : ℝ)
  hlog_u : Real.log (n : ℝ) ≤ u
  hr0 : 0 < r
  hsqrt : r ^ 2 ≤ (n : ℝ)
  hpi_pos : 0 < pi_lb
  hpi : pi_lb ≤ Real.pi
  hexp : Real.exp (-t_critical * l ^ 2) ≤ exp_ub
  hub :
    ((2 * u) / r) * exp_ub * (u / (2 * pi_lb)) ≤ Full.prime_heat_pp_term_ub n

lemma prime_heat_weight_term_le_pp_ub_of_bounds {n : ℕ} (h : PrimeHeatEnvelopeBounds n) :
    prime_heat_weight_term n ≤ Full.prime_heat_pp_term_ub n := by
  have h_env :
      prime_heat_envelope n ≤ prime_heat_envelope_ub n h.l h.u := by
    exact prime_heat_envelope_le_of_log_bounds (n := n) (l := h.l) (u := h.u)
      h.hl0 h.hu0 h.hlog_l h.hlog_u
  have h_ub :
      prime_heat_envelope_ub n h.l h.u ≤
        ((2 * h.u) / h.r) * h.exp_ub * (h.u / (2 * h.pi_lb)) := by
    exact prime_heat_envelope_ub_le_of_bounds (n := n) (l := h.l) (u := h.u)
      (r := h.r) (exp_ub := h.exp_ub) (pi_lb := h.pi_lb)
      h.hu0 h.hr0 h.hsqrt h.hpi_pos h.hpi h.hexp
  exact (prime_heat_weight_term_le_envelope n).trans (h_env.trans (h_ub.trans h.hub))

def pi_lb : ℝ := (3.14159265358979323846 : ℝ)

lemma pi_lb_le_pi : pi_lb ≤ Real.pi := by
  exact (le_of_lt Real.pi_gt_d20)

lemma pi_lb_pos : 0 < pi_lb := by
  norm_num [pi_lb]

def l2 : ℝ := (6931471805599451 : ℝ) / (10 ^ 16 : ℝ)
def u2 : ℝ := (6931471805599455 : ℝ) / (10 ^ 16 : ℝ)
def r2 : ℝ := (14142135623730950 : ℝ) / (10 ^ 16 : ℝ)

def l3 : ℝ := (10986122886681095 : ℝ) / (10 ^ 16 : ℝ)
def u3 : ℝ := (10986122886681099 : ℝ) / (10 ^ 16 : ℝ)
def r3 : ℝ := (17320508075688771 : ℝ) / (10 ^ 16 : ℝ)

def l5 : ℝ := (16094379124340999 : ℝ) / (10 ^ 16 : ℝ)
def u5 : ℝ := (16094379124341009 : ℝ) / (10 ^ 16 : ℝ)
def r5 : ℝ := (22360679774997896 : ℝ) / (10 ^ 16 : ℝ)

def b3 : ℝ := (173205080756887725 : ℝ) / (10 ^ 17 : ℝ)
def b5 : ℝ := (22360679774997893 : ℝ) / (10 ^ 16 : ℝ)

def bound2_num : ℚ :=
  440817562082005722345823632201056256000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def bound2_den : ℚ :=
  4380982826493731039176157907850836754832723879375901136721619519243737752838576106949814550952667282123222810135382419956462387662011860296250236727390629913440367424406406478437831934428655787809513900563741697010718108721415033971693818865313397228115807054271285826087206051663558168906074583030113927658556764007640701295309058132850205457868365179246932954601316298769845480483683676414282504305410329

def bound3_num : ℚ :=
  12164665485001279709096481604163771608911052800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def bound3_den : ℚ :=
  65727551899108161592470544635739725398881972163518645601169036669608542777317764063828427033682702760521860607394670636494812667058115671093804800160355593783254014999282991678259709711493979636235023128859505101792746650926960407344325966571436188725390757207860774641340370106342257553313339660366403524666945347963942263507940554012337785043876970587483880325888926251682953733714435628911

def bound5_num : ℚ :=
  33985405706229735397935812137087019384832000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def bound5_den : ℚ :=
  135931842094016036463084394020908948213437706354087710675598405028321463243654891526598013512079553110543912100275476762999428070259191300679383664061553950942476365505480659892105010069435592426165108686209123973910445033820293751619329537127982272646889675552723711414502360644459639309946299823446986640861067518397536357956368006332749301759038873792190550914647882886313481039874098857558071670191300418603013904738751959038982410120551086037359497286740328042350282699811

def ub2_q : ℚ := (100620700774307542113561453335 : ℚ) / Full.prime_heat_pp_term_ub_den
def ub3_q : ℚ := (185077112010410077536093353956 : ℚ) / Full.prime_heat_pp_term_ub_den
def ub5_q : ℚ := (250017988299783666672482240756 : ℚ) / Full.prime_heat_pp_term_ub_den

lemma prime_heat_pp_term_ub_q_get_bucket_0_part1_two :
    Full.prime_heat_pp_term_ub_q_get_bucket_0_part1 2 = ub2_q := by
  rfl

lemma prime_heat_pp_term_ub_q_get_bucket_0_part1_three :
    Full.prime_heat_pp_term_ub_q_get_bucket_0_part1 3 = ub3_q := by
  rfl

lemma prime_heat_pp_term_ub_q_get_bucket_0_part1_five :
    Full.prime_heat_pp_term_ub_q_get_bucket_0_part1 5 = ub5_q := by
  rfl

lemma exp_l2_le_two : Real.exp l2 ≤ (2 : ℝ) := by
  have hx0 : 0 ≤ l2 := by norm_num [l2]
  have hx1 : l2 ≤ 1 := by norm_num [l2]
  have h' :
      (∑ m ∈ Finset.range 18, l2 ^ m / (Nat.factorial m)) +
          l2 ^ 18 * (18 + 1) / (Nat.factorial 18 * 18) ≤
        (2 : ℝ) := by
    norm_num [l2]
  exact exp_le_of_taylor_bound (x := l2) (b := (2 : ℝ)) hx0 hx1 (n := 18) (by decide) h'

lemma two_le_exp_u2 : (2 : ℝ) ≤ Real.exp u2 := by
  have hx0 : 0 ≤ u2 := by norm_num [u2]
  have hsum :
      (2 : ℝ) ≤ ∑ m ∈ Finset.range 18, u2 ^ m / (Nat.factorial m) := by
    norm_num [u2]
  have hle :
      ∑ m ∈ Finset.range 18, u2 ^ m / (Nat.factorial m) ≤ Real.exp u2 := by
    simpa using (Real.sum_le_exp_of_nonneg hx0 18)
  exact le_trans hsum hle

lemma exp_l3_div_two_le_b3 : Real.exp (l3 / 2) ≤ b3 := by
  have hx0 : 0 ≤ l3 / 2 := by norm_num [l3]
  have hx1 : l3 / 2 ≤ 1 := by norm_num [l3]
  have h' :
      (∑ m ∈ Finset.range 14, (l3 / 2) ^ m / (Nat.factorial m)) +
          (l3 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
        b3 := by
    norm_num [l3, b3]
  exact exp_le_of_taylor_bound (x := l3 / 2) (b := b3) hx0 hx1 (n := 14) (by decide) h'

lemma exp_l3_le_three : Real.exp l3 ≤ (3 : ℝ) := by
  have hpow :
      Real.exp l3 ≤ b3 ^ 2 := by
    have hx0 : 0 ≤ l3 := by norm_num [l3]
    have hx1 : l3 / 2 ≤ 1 := by norm_num [l3]
    exact exp_le_pow_of_taylor_bound_div (x := l3) (b := b3) (n := 2) (k := 14)
      (by decide) (by decide) hx0 hx1 (by
        have h' :
            (∑ m ∈ Finset.range 14, (l3 / 2) ^ m / (Nat.factorial m)) +
                (l3 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
              b3 := by
          norm_num [l3, b3]
        simpa using h')
  have hb : b3 ^ 2 ≤ (3 : ℝ) := by
    norm_num [b3]
  exact hpow.trans hb

lemma three_le_exp_u3 : (3 : ℝ) ≤ Real.exp u3 := by
  have hx0 : 0 ≤ u3 := by norm_num [u3]
  have hsum :
      (3 : ℝ) ≤ ∑ m ∈ Finset.range 20, u3 ^ m / (Nat.factorial m) := by
    norm_num [u3]
  have hle :
      ∑ m ∈ Finset.range 20, u3 ^ m / (Nat.factorial m) ≤ Real.exp u3 := by
    simpa using (Real.sum_le_exp_of_nonneg hx0 20)
  exact le_trans hsum hle

lemma exp_l5_div_two_le_b5 : Real.exp (l5 / 2) ≤ b5 := by
  have hx0 : 0 ≤ l5 / 2 := by norm_num [l5]
  have hx1 : l5 / 2 ≤ 1 := by norm_num [l5]
  have h' :
      (∑ m ∈ Finset.range 16, (l5 / 2) ^ m / (Nat.factorial m)) +
          (l5 / 2) ^ 16 * (16 + 1) / (Nat.factorial 16 * 16) ≤
        b5 := by
    norm_num [l5, b5]
  exact exp_le_of_taylor_bound (x := l5 / 2) (b := b5) hx0 hx1 (n := 16) (by decide) h'

lemma exp_l5_le_five : Real.exp l5 ≤ (5 : ℝ) := by
  have hpow :
      Real.exp l5 ≤ b5 ^ 2 := by
    have hx0 : 0 ≤ l5 := by norm_num [l5]
    have hx1 : l5 / 2 ≤ 1 := by norm_num [l5]
    exact exp_le_pow_of_taylor_bound_div (x := l5) (b := b5) (n := 2) (k := 16)
      (by decide) (by decide) hx0 hx1 (by
        have h' :
            (∑ m ∈ Finset.range 16, (l5 / 2) ^ m / (Nat.factorial m)) +
                (l5 / 2) ^ 16 * (16 + 1) / (Nat.factorial 16 * 16) ≤
              b5 := by
          norm_num [l5, b5]
        simpa using h')
  have hb : b5 ^ 2 ≤ (5 : ℝ) := by
    norm_num [b5]
  exact hpow.trans hb

lemma five_le_exp_u5 : (5 : ℝ) ≤ Real.exp u5 := by
  have hx0 : 0 ≤ u5 := by norm_num [u5]
  have hsum :
      (5 : ℝ) ≤ ∑ m ∈ Finset.range 22, u5 ^ m / (Nat.factorial m) := by
    norm_num [u5]
  have hle :
      ∑ m ∈ Finset.range 22, u5 ^ m / (Nat.factorial m) ≤ Real.exp u5 := by
    simpa using (Real.sum_le_exp_of_nonneg hx0 22)
  exact le_trans hsum hle

lemma l2_le_log_two : l2 ≤ Real.log 2 := by
  exact le_log_nat_of_exp_le (n := 2) (by decide) exp_l2_le_two

lemma log_two_le_u2 : Real.log 2 ≤ u2 := by
  exact log_nat_le_of_le_exp (n := 2) (by decide) two_le_exp_u2

lemma l3_le_log_three : l3 ≤ Real.log 3 := by
  exact le_log_nat_of_exp_le (n := 3) (by decide) exp_l3_le_three

lemma log_three_le_u3 : Real.log 3 ≤ u3 := by
  exact log_nat_le_of_le_exp (n := 3) (by decide) three_le_exp_u3

lemma l5_le_log_five : l5 ≤ Real.log 5 := by
  exact le_log_nat_of_exp_le (n := 5) (by decide) exp_l5_le_five

lemma log_five_le_u5 : Real.log 5 ≤ u5 := by
  exact log_nat_le_of_le_exp (n := 5) (by decide) five_le_exp_u5

lemma r2_sq_le : r2 ^ 2 ≤ (2 : ℝ) := by norm_num [r2]
lemma r3_sq_le : r3 ^ 2 ≤ (3 : ℝ) := by norm_num [r3]
lemma r5_sq_le : r5 ^ 2 ≤ (5 : ℝ) := by norm_num [r5]

lemma r2_pos : 0 < r2 := by norm_num [r2]
lemma r3_pos : 0 < r3 := by norm_num [r3]
lemma r5_pos : 0 < r5 := by norm_num [r5]

set_option maxHeartbeats 0 in
lemma prime_heat_pp_term_ub_two_eq :
    Full.prime_heat_pp_term_ub 2 =
      (ub2_q : ℝ) := by
  change ((Full.prime_heat_pp_term_ub_q_get 2 : ℚ) : ℝ) = (ub2_q : ℝ)
  exact_mod_cast (by
    simp [Full.prime_heat_pp_term_ub_q_get,
      Full.prime_heat_pp_term_bucket_index, Full.prime_heat_pp_term_bucket_width,
      Full.prime_heat_pp_term_ub_q_get_bucket_0, prime_heat_pp_term_ub_q_get_bucket_0_part1_two,
      ub2_q, Full.prime_heat_pp_term_ub_den])

set_option maxHeartbeats 0 in
lemma prime_heat_pp_term_ub_three_eq :
    Full.prime_heat_pp_term_ub 3 =
      (ub3_q : ℝ) := by
  change ((Full.prime_heat_pp_term_ub_q_get 3 : ℚ) : ℝ) = (ub3_q : ℝ)
  exact_mod_cast (by
    simp [Full.prime_heat_pp_term_ub_q_get,
      Full.prime_heat_pp_term_bucket_index, Full.prime_heat_pp_term_bucket_width,
      Full.prime_heat_pp_term_ub_q_get_bucket_0, prime_heat_pp_term_ub_q_get_bucket_0_part1_three,
      ub3_q, Full.prime_heat_pp_term_ub_den])

set_option maxHeartbeats 0 in
lemma prime_heat_pp_term_ub_five_eq :
    Full.prime_heat_pp_term_ub 5 =
      (ub5_q : ℝ) := by
  change ((Full.prime_heat_pp_term_ub_q_get 5 : ℚ) : ℝ) = (ub5_q : ℝ)
  exact_mod_cast (by
    simp [Full.prime_heat_pp_term_ub_q_get,
      Full.prime_heat_pp_term_bucket_index, Full.prime_heat_pp_term_bucket_width,
      Full.prime_heat_pp_term_ub_q_get_bucket_0, prime_heat_pp_term_ub_q_get_bucket_0_part1_five,
      ub5_q, Full.prime_heat_pp_term_ub_den])

def envelope_bounds_two : PrimeHeatEnvelopeBounds 2 :=
  { l := l2
    u := u2
    r := r2
    exp_ub := 1 / (∑ m ∈ Finset.range 12, (t_critical * l2 ^ 2) ^ m / (Nat.factorial m))
    pi_lb := pi_lb
    hl0 := by norm_num [l2]
    hu0 := by norm_num [u2]
    hlog_l := l2_le_log_two
    hlog_u := log_two_le_u2
    hr0 := r2_pos
    hsqrt := by simpa using r2_sq_le
    hpi_pos := pi_lb_pos
    hpi := pi_lb_le_pi
    hexp := by
      have hc : 0 ≤ t_critical * l2 ^ 2 := by
        have ht : 0 ≤ t_critical := by norm_num [t_critical]
        have hl : 0 ≤ l2 ^ 2 := by nlinarith
        nlinarith
      simpa using (exp_neg_le_inv_sum (c := t_critical * l2 ^ 2) hc (n := 12) (by decide))
    hub := by
      have hpp := prime_heat_pp_term_ub_two_eq
      have hval :
          ((2 * u2) / r2) *
              (1 / (∑ m ∈ Finset.range 12, (t_critical * l2 ^ 2) ^ m / (Nat.factorial m))) *
              (u2 / (2 * pi_lb)) =
            ((bound2_num : ℝ) / (bound2_den : ℝ)) := by
        norm_num [t_critical, l2, u2, r2, pi_lb, bound2_num, bound2_den]
      have hrat :
          (bound2_num / bound2_den) ≤ ub2_q := by
        native_decide
      have hrat' :
          ((bound2_num : ℝ) / (bound2_den : ℝ)) ≤ (ub2_q : ℝ) := by
        exact_mod_cast hrat
      have hrat'' :
          ((bound2_num : ℝ) / (bound2_den : ℝ)) ≤
            Full.prime_heat_pp_term_ub 2 := by
        simpa [hpp] using hrat'
      exact hval.le.trans hrat'' }

def envelope_bounds_three : PrimeHeatEnvelopeBounds 3 :=
  { l := l3
    u := u3
    r := r3
    exp_ub := 1 / (∑ m ∈ Finset.range 12, (t_critical * l3 ^ 2) ^ m / (Nat.factorial m))
    pi_lb := pi_lb
    hl0 := by norm_num [l3]
    hu0 := by norm_num [u3]
    hlog_l := l3_le_log_three
    hlog_u := log_three_le_u3
    hr0 := r3_pos
    hsqrt := by simpa using r3_sq_le
    hpi_pos := pi_lb_pos
    hpi := pi_lb_le_pi
    hexp := by
      have hc : 0 ≤ t_critical * l3 ^ 2 := by
        have ht : 0 ≤ t_critical := by norm_num [t_critical]
        have hl : 0 ≤ l3 ^ 2 := by nlinarith
        nlinarith
      simpa using (exp_neg_le_inv_sum (c := t_critical * l3 ^ 2) hc (n := 12) (by decide))
    hub := by
      have hpp := prime_heat_pp_term_ub_three_eq
      have hval :
          ((2 * u3) / r3) *
              (1 / (∑ m ∈ Finset.range 12, (t_critical * l3 ^ 2) ^ m / (Nat.factorial m))) *
              (u3 / (2 * pi_lb)) =
            ((bound3_num : ℝ) / (bound3_den : ℝ)) := by
        norm_num [t_critical, l3, u3, r3, pi_lb, bound3_num, bound3_den]
      have hrat :
          (bound3_num / bound3_den) ≤ ub3_q := by
        native_decide
      have hrat' :
          ((bound3_num : ℝ) / (bound3_den : ℝ)) ≤ (ub3_q : ℝ) := by
        exact_mod_cast hrat
      have hrat'' :
          ((bound3_num : ℝ) / (bound3_den : ℝ)) ≤
            Full.prime_heat_pp_term_ub 3 := by
        simpa [hpp] using hrat'
      exact hval.le.trans hrat'' }

def envelope_bounds_five : PrimeHeatEnvelopeBounds 5 :=
  { l := l5
    u := u5
    r := r5
    exp_ub := 1 / (∑ m ∈ Finset.range 14, (t_critical * l5 ^ 2) ^ m / (Nat.factorial m))
    pi_lb := pi_lb
    hl0 := by norm_num [l5]
    hu0 := by norm_num [u5]
    hlog_l := l5_le_log_five
    hlog_u := log_five_le_u5
    hr0 := r5_pos
    hsqrt := by simpa using r5_sq_le
    hpi_pos := pi_lb_pos
    hpi := pi_lb_le_pi
    hexp := by
      have hc : 0 ≤ t_critical * l5 ^ 2 := by
        have ht : 0 ≤ t_critical := by norm_num [t_critical]
        have hl : 0 ≤ l5 ^ 2 := by nlinarith
        nlinarith
      simpa using (exp_neg_le_inv_sum (c := t_critical * l5 ^ 2) hc (n := 14) (by decide))
    hub := by
      have hpp := prime_heat_pp_term_ub_five_eq
      have hval :
          ((2 * u5) / r5) *
              (1 / (∑ m ∈ Finset.range 14, (t_critical * l5 ^ 2) ^ m / (Nat.factorial m))) *
              (u5 / (2 * pi_lb)) =
            ((bound5_num : ℝ) / (bound5_den : ℝ)) := by
        norm_num [t_critical, l5, u5, r5, pi_lb, bound5_num, bound5_den]
      have hrat :
          (bound5_num / bound5_den) ≤ ub5_q := by
        native_decide
      have hrat' :
          ((bound5_num : ℝ) / (bound5_den : ℝ)) ≤ (ub5_q : ℝ) := by
        exact_mod_cast hrat
      have hrat'' :
          ((bound5_num : ℝ) / (bound5_den : ℝ)) ≤
            Full.prime_heat_pp_term_ub 5 := by
        simpa [hpp] using hrat'
      exact hval.le.trans hrat'' }

lemma prime_heat_weight_term_le_pp_ub_two :
    prime_heat_weight_term 2 ≤ Full.prime_heat_pp_term_ub 2 := by
  exact prime_heat_weight_term_le_pp_ub_of_bounds envelope_bounds_two

lemma prime_heat_weight_term_le_pp_ub_three :
    prime_heat_weight_term 3 ≤ Full.prime_heat_pp_term_ub 3 := by
  exact prime_heat_weight_term_le_pp_ub_of_bounds envelope_bounds_three

lemma prime_heat_weight_term_le_pp_ub_five :
    prime_heat_weight_term 5 ≤ Full.prime_heat_pp_term_ub 5 := by
  exact prime_heat_weight_term_le_pp_ub_of_bounds envelope_bounds_five

end Q3.Proofs.PrimeCert
