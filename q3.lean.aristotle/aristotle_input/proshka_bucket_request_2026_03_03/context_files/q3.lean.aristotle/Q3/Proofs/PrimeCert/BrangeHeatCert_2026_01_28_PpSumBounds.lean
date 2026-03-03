import Mathlib
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Intervals
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowFull
set_option maxHeartbeats 0

/-!
Precomputed bucket-sum bounds for prime-power interval data (t_critical, tau = 0).
These lemmas compare the per-bucket sum constants against the bucket upper bounds.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

lemma prime_heat_pp_term_ub_q_sum_bucket_le_0 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_0 ≤ (4.00453633676041 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_0, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_1 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_1 ≤ (0.00030761483806 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_1, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_2 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_2 ≤ (0.00004721430942 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_2, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_3 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_3 ≤ (0.00001395858700 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_3, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_4 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_4 ≤ (0.00000550840392 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_4, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_5 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_5 ≤ (0.00000265320611 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_5, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_6 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_6 ≤ (0.00000137132311 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_6, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_7 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_7 ≤ (0.00000083234195 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_7, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_8 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_8 ≤ (0.00000050531745 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_8, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_9 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_9 ≤ (0.00000033379971 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_9, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_10 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_10 ≤ (0.00000022318380 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_10, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_11 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_11 ≤ (0.00000015506125 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_11, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_12 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_12 ≤ (0.00000011424741 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_12, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_13 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_13 ≤ (0.00000008393825 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_13, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_14 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_14 ≤ (0.00000006256147 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_14, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_15 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_15 ≤ (0.00000004811040 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_15, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_16 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_16 ≤ (0.00000003665735 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_16, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_17 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_17 ≤ (0.00000003009306 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_17, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_18 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_18 ≤ (0.00000002363038 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_18, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_19 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_19 ≤ (0.00000001885901 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_19, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_20 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_20 ≤ (0.00000001559647 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_20, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_21 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_21 ≤ (0.00000001270747 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_21, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_22 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_22 ≤ (0.00000001066836 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_22, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_23 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_23 ≤ (0.00000000857497 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_23, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_24 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_24 ≤ (0.00000000760418 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_24, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_25 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_25 ≤ (0.00000000622555 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_25, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_26 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_26 ≤ (0.00000000539070 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_26, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_27 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_27 ≤ (0.00000000456168 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_27, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_28 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_28 ≤ (0.00000000394420 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_28, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_29 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_29 ≤ (0.00000000334299 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_29, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_30 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_30 ≤ (0.00000000302435 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_30, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_31 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_31 ≤ (0.00000000266004 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_31, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_32 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_32 ≤ (0.00000000230465 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_32, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_33 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_33 ≤ (0.00000000198625 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_33, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_34 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_34 ≤ (0.00000000179408 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_34, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_35 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_35 ≤ (0.00000000156468 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_35, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_36 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_36 ≤ (0.00000000136550 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_36, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_37 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_37 ≤ (0.00000000123830 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_37, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_38 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_38 ≤ (0.00000000109424 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_38, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_39 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_39 ≤ (0.00000000101569 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_39, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_40 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_40 ≤ (0.00000000086686 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_40, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_41 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_41 ≤ (0.00000000080708 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_41, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_42 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_42 ≤ (0.00000000072498 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_42, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_43 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_43 ≤ (0.00000000066406 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_43, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_44 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_44 ≤ (0.00000000059153 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_44, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_45 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_45 ≤ (0.00000000052971 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_45, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_46 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_46 ≤ (0.00000000049022 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_46, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_47 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_47 ≤ (0.00000000045811 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_47, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_48 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_48 ≤ (0.00000000040729 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_48, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_49 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_49 ≤ (0.00000000037902 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_49, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_50 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_50 ≤ (0.00000000033924 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_50, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_51 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_51 ≤ (0.00000000031877 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_51, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_52 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_52 ≤ (0.00000000029138 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_52, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_53 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_53 ≤ (0.00000000026273 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_53, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_54 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_54 ≤ (0.00000000024346 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_54, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_55 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_55 ≤ (0.00000000022513 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_55, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_56 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_56 ≤ (0.00000000020759 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_56, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_57 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_57 ≤ (0.00000000019831 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_57, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_58 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_58 ≤ (0.00000000018223 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_58, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_59 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_59 ≤ (0.00000000016599 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_59, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_60 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_60 ≤ (0.00000000015748 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_60, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_61 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_61 ≤ (0.00000000014444 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_61, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_62 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_62 ≤ (0.00000000013067 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_62, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_63 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_63 ≤ (0.00000000012273 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_63, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_64 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_64 ≤ (0.00000000011819 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_64, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_65 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_65 ≤ (0.00000000010717 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_65, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_66 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_66 ≤ (0.00000000010190 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_66, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_67 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_67 ≤ (0.00000000009667 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_67, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_68 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_68 ≤ (0.00000000009039 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_68, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_69 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_69 ≤ (0.00000000008203 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_69, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_70 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_70 ≤ (0.00000000008085 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_70, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_71 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_71 ≤ (0.00000000007196 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_71, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_72 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_72 ≤ (0.00000000007119 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_72, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_73 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_73 ≤ (0.00000000006544 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_73, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_74 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_74 ≤ (0.00000000005872 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_74, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_75 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_75 ≤ (0.00000000005793 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_75, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_76 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_76 ≤ (0.00000000005581 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_76, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_77 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_77 ≤ (0.00000000005133 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_77, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_78 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_78 ≤ (0.00000000004867 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_78, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_79 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_79 ≤ (0.00000000004643 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_79, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_80 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_80 ≤ (0.00000000004316 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_80, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_81 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_81 ≤ (0.00000000004091 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_81, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_82 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_82 ≤ (0.00000000003947 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_82, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_83 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_83 ≤ (0.00000000003655 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_83, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_84 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_84 ≤ (0.00000000003458 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_84, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_85 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_85 ≤ (0.00000000003270 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_85, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_86 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_86 ≤ (0.00000000003227 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_86, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_87 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_87 ≤ (0.00000000002964 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_87, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_88 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_88 ≤ (0.00000000002834 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_88, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_89 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_89 ≤ (0.00000000002648 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_89, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_90 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_90 ≤ (0.00000000002633 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_90, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_91 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_91 ≤ (0.00000000002360 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_91, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_92 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_92 ≤ (0.00000000002350 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_92, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_93 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_93 ≤ (0.00000000002159 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_93, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_94 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_94 ≤ (0.00000000002079 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_94, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_95 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_95 ≤ (0.00000000001958 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_95, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_96 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_96 ≤ (0.00000000001924 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_96, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_97 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_97 ≤ (0.00000000001799 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_97, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_98 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_98 ≤ (0.00000000001702 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_98, Full.prime_heat_pp_term_ub_den]
  norm_num

lemma prime_heat_pp_term_ub_q_sum_bucket_le_99 :
    Full.prime_heat_pp_term_ub_q_sum_bucket_99 ≤ (0.00000000001651 : ℚ) := by
  simp [Full.prime_heat_pp_term_ub_q_sum_bucket_99, Full.prime_heat_pp_term_ub_den]
  norm_num

end Q3.Proofs.PrimeCert
