import Q3.Proofs.PSD_CenteredCoeffDictionaryImport
import Q3.Proofs.PSD_PenaltyCertificate
import Q3.Proofs.PrimeCert.IntervalLemmas

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step32G Q-row hbox certificates.

The scalar certificates use `Real.exp_bound` at Taylor order 23 after
splitting each active exponent as `exp x = exp (x / 2) ^ 2`, so all
Taylor arguments satisfy `|x / 2| <= 1`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffQRowImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport

private def qrowTaylorS (x : Real) (n : Nat) : Real :=
  ∑ m ∈ Finset.range n, (x / 2) ^ m / (Nat.factorial m)

private def qrowTaylorE (x : Real) (n : Nat) : Real :=
  |x / 2| ^ n * ((n.succ : Real) / (Nat.factorial n * n))

private lemma exp_abs_sub_le_of_half_taylor
    (x m r : Real) {n : Nat}
    (hn : 0 < n)
    (hy : |x / 2| <= (1 : Real))
    (hlow0 : 0 <= qrowTaylorS x n - qrowTaylorE x n)
    (htargetLow : m - r <= (qrowTaylorS x n - qrowTaylorE x n) ^ 2)
    (htargetHigh : (qrowTaylorS x n + qrowTaylorE x n) ^ 2 <= m + r) :
    |Real.exp x - m| <= r := by
  have hbound : |Real.exp (x / 2) - qrowTaylorS x n| <= qrowTaylorE x n := by
    simpa [qrowTaylorS, qrowTaylorE] using
      (Real.exp_bound (x := x / 2) hy (n := n) hn)
  have hlow : qrowTaylorS x n - qrowTaylorE x n <= Real.exp (x / 2) := by
    have h := (abs_sub_le_iff.mp hbound).2
    linarith
  have hhigh : Real.exp (x / 2) <= qrowTaylorS x n + qrowTaylorE x n := by
    have h := (abs_sub_le_iff.mp hbound).1
    linarith
  have hexp : Real.exp x = Real.exp (x / 2) ^ 2 := by
    exact Q3.Proofs.PrimeCert.exp_eq_pow_div_nat x (n := 2) (by norm_num)
  have hpowLow : (qrowTaylorS x n - qrowTaylorE x n) ^ 2 <= Real.exp x := by
    rw [hexp]
    exact pow_le_pow_left₀ hlow0 hlow 2
  have hpowHigh : Real.exp x <= (qrowTaylorS x n + qrowTaylorE x n) ^ 2 := by
    rw [hexp]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hhigh 2
  rw [abs_sub_le_iff]
  constructor <;> nlinarith

private lemma qrow_bound_0_0 :
    |Real.exp ((-27 : Real) / (20 : Real)) - ((2592402606458915071 : Real) / (10000000000000000000 : Real))| <= ((7571732611468718957 : Real) / (1000000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-27 : Real) / (20 : Real)) ((2592402606458915071 : Real) / (10000000000000000000 : Real)) ((7571732611468718957 : Real) / (1000000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_1 :
    |Real.exp ((-49 : Real) / (40 : Real)) - ((2937577003235328221 : Real) / (10000000000000000000 : Real))| <= ((1440350335559975343 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-49 : Real) / (40 : Real)) ((2937577003235328221 : Real) / (10000000000000000000 : Real)) ((1440350335559975343 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_2 :
    |Real.exp ((-11 : Real) / (10 : Real)) - ((3328710836980795507 : Real) / (10000000000000000000 : Real))| <= ((131553876270408003 : Real) / (40000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-11 : Real) / (10 : Real)) ((3328710836980795507 : Real) / (10000000000000000000 : Real)) ((131553876270408003 : Real) / (40000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_3 :
    |Real.exp ((-39 : Real) / (40 : Real)) - ((1885961767815784451 : Real) / (5000000000000000000 : Real))| <= ((2318261080449556439 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-39 : Real) / (40 : Real)) ((1885961767815784451 : Real) / (5000000000000000000 : Real)) ((2318261080449556439 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_4 :
    |Real.exp ((-17 : Real) / (20 : Real)) - ((4274149319487266507 : Real) / (10000000000000000000 : Real))| <= ((996022542158421487 : Real) / (50000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-17 : Real) / (20 : Real)) ((4274149319487266507 : Real) / (10000000000000000000 : Real)) ((996022542158421487 : Real) / (50000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_5 :
    |Real.exp ((-29 : Real) / (40 : Real)) - ((4843245689553624667 : Real) / (10000000000000000000 : Real))| <= ((2999945324456514801 : Real) / (1000000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-29 : Real) / (40 : Real)) ((4843245689553624667 : Real) / (10000000000000000000 : Real)) ((2999945324456514801 : Real) / (1000000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_6 :
    |Real.exp ((-3 : Real) / (5 : Real)) - ((2744058180470131947 : Real) / (5000000000000000000 : Real))| <= ((34582767168368823 : Real) / (800000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-3 : Real) / (5 : Real)) ((2744058180470131947 : Real) / (5000000000000000000 : Real)) ((34582767168368823 : Real) / (800000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_7 :
    |Real.exp ((-19 : Real) / (40 : Real)) - ((6218850564650201251 : Real) / (10000000000000000000 : Real))| <= ((1604892412006029 : Real) / (32000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-19 : Real) / (40 : Real)) ((6218850564650201251 : Real) / (10000000000000000000 : Real)) ((1604892412006029 : Real) / (32000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_8 :
    |Real.exp ((-7 : Real) / (20 : Real)) - ((1761720224296783599 : Real) / (2500000000000000000 : Real))| <= ((1717741035123317873 : Real) / (50000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-7 : Real) / (20 : Real)) ((1761720224296783599 : Real) / (2500000000000000000 : Real)) ((1717741035123317873 : Real) / (50000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_9 :
    |Real.exp ((-9 : Real) / (40 : Real)) - ((7985162187593770611 : Real) / (10000000000000000000 : Real))| <= ((2858067363135478609 : Real) / (50000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-9 : Real) / (40 : Real)) ((7985162187593770611 : Real) / (10000000000000000000 : Real)) ((2858067363135478609 : Real) / (50000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_10 :
    |Real.exp ((-1 : Real) / (10 : Real)) - ((4524187090179798143 : Real) / (5000000000000000000 : Real))| <= ((554357509959893169 : Real) / (10000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-1 : Real) / (10 : Real)) ((4524187090179798143 : Real) / (5000000000000000000 : Real)) ((554357509959893169 : Real) / (10000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_11 :
    |Real.exp ((1 : Real) / (40 : Real)) - ((512657560262214429 : Real) / (500000000000000000 : Real))| <= ((5932197897596789653 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((1 : Real) / (40 : Real)) ((512657560262214429 : Real) / (500000000000000000 : Real)) ((5932197897596789653 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_12 :
    |Real.exp ((3 : Real) / (20 : Real)) - ((580917121364141531 : Real) / (500000000000000000 : Real))| <= ((1226166202265933193 : Real) / (10000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((3 : Real) / (20 : Real)) ((580917121364141531 : Real) / (500000000000000000 : Real)) ((1226166202265933193 : Real) / (10000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_13 :
    |Real.exp ((11 : Real) / (40 : Real)) - ((658265337433810771 : Real) / (500000000000000000 : Real))| <= ((122946382455083509 : Real) / (1000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((11 : Real) / (40 : Real)) ((658265337433810771 : Real) / (500000000000000000 : Real)) ((122946382455083509 : Real) / (1000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_14 :
    |Real.exp ((2 : Real) / (5 : Real)) - ((372956174410317587 : Real) / (250000000000000000 : Real))| <= ((3017514707733792551 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((2 : Real) / (5 : Real)) ((372956174410317587 : Real) / (250000000000000000 : Real)) ((3017514707733792551 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_15 :
    |Real.exp ((21 : Real) / (40 : Real)) - ((1690458848379091439 : Real) / (1000000000000000000 : Real))| <= ((7950403618917092141 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((21 : Real) / (40 : Real)) ((1690458848379091439 : Real) / (1000000000000000000 : Real)) ((7950403618917092141 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_16 :
    |Real.exp ((13 : Real) / (20 : Real)) - ((478885207253473999 : Real) / (250000000000000000 : Real))| <= ((115854216041919933 : Real) / (1562500000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((13 : Real) / (20 : Real)) ((478885207253473999 : Real) / (250000000000000000 : Real)) ((115854216041919933 : Real) / (1562500000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_17 :
    |Real.exp ((31 : Real) / (40 : Real)) - ((2170592127183442521 : Real) / (1000000000000000000 : Real))| <= ((676359539077902281 : Real) / (5000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((31 : Real) / (40 : Real)) ((2170592127183442521 : Real) / (1000000000000000000 : Real)) ((676359539077902281 : Real) / (5000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_18 :
    |Real.exp ((9 : Real) / (10 : Real)) - ((2459603111156949851 : Real) / (1000000000000000000 : Real))| <= ((3361998734700175301 : Real) / (10000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((9 : Real) / (10 : Real)) ((2459603111156949851 : Real) / (1000000000000000000 : Real)) ((3361998734700175301 : Real) / (10000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_19 :
    |Real.exp ((41 : Real) / (40 : Real)) - ((2787095460565850669 : Real) / (1000000000000000000 : Real))| <= ((1243922122709885183 : Real) / (12500000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((41 : Real) / (40 : Real)) ((2787095460565850669 : Real) / (1000000000000000000 : Real)) ((1243922122709885183 : Real) / (12500000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_20 :
    |Real.exp ((23 : Real) / (20 : Real)) - ((25265543277518141 : Real) / (8000000000000000 : Real))| <= ((136253503153659313 : Real) / (5000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((23 : Real) / (20 : Real)) ((25265543277518141 : Real) / (8000000000000000 : Real)) ((136253503153659313 : Real) / (5000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_21 :
    |Real.exp ((51 : Real) / (40 : Real)) - ((1789350705050789747 : Real) / (500000000000000000 : Real))| <= ((254076669172690137 : Real) / (1250000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((51 : Real) / (40 : Real)) ((1789350705050789747 : Real) / (500000000000000000 : Real)) ((254076669172690137 : Real) / (1250000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_0_22 :
    |Real.exp ((7 : Real) / (5 : Real)) - ((2027599983422337271 : Real) / (500000000000000000 : Real))| <= ((4361205445197551383 : Real) / (50000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((7 : Real) / (5 : Real)) ((2027599983422337271 : Real) / (500000000000000000 : Real)) ((4361205445197551383 : Real) / (50000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_0 :
    |Real.exp ((27 : Real) / (20 : Real)) - ((3857425530696974469 : Real) / (1000000000000000000 : Real))| <= ((1618611611062559049 : Real) / (10000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((27 : Real) / (20 : Real)) ((3857425530696974469 : Real) / (1000000000000000000 : Real)) ((1618611611062559049 : Real) / (10000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_1 :
    |Real.exp ((49 : Real) / (40 : Real)) - ((1702083041395409557 : Real) / (500000000000000000 : Real))| <= ((1276798562558104903 : Real) / (10000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((49 : Real) / (40 : Real)) ((1702083041395409557 : Real) / (500000000000000000 : Real)) ((1276798562558104903 : Real) / (10000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_2 :
    |Real.exp ((11 : Real) / (10 : Real)) - ((3004166023946432951 : Real) / (1000000000000000000 : Real))| <= ((201323010143308877 : Real) / (1250000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((11 : Real) / (10 : Real)) ((3004166023946432951 : Real) / (1000000000000000000 : Real)) ((201323010143308877 : Real) / (1250000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_3 :
    |Real.exp ((39 : Real) / (40 : Real)) - ((662791802745651637 : Real) / (250000000000000000 : Real))| <= ((911918750815046811 : Real) / (5000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((39 : Real) / (40 : Real)) ((662791802745651637 : Real) / (250000000000000000 : Real)) ((911918750815046811 : Real) / (5000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_4 :
    |Real.exp ((17 : Real) / (20 : Real)) - ((584911712981497689 : Real) / (250000000000000000 : Real))| <= ((1808547271184185207 : Real) / (10000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((17 : Real) / (20 : Real)) ((584911712981497689 : Real) / (250000000000000000 : Real)) ((1808547271184185207 : Real) / (10000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_5 :
    |Real.exp ((29 : Real) / (40 : Real)) - ((1032365549983243369 : Real) / (500000000000000000 : Real))| <= ((1044911873681930337 : Real) / (5000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((29 : Real) / (40 : Real)) ((1032365549983243369 : Real) / (500000000000000000 : Real)) ((1044911873681930337 : Real) / (5000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_6 :
    |Real.exp ((3 : Real) / (5 : Real)) - ((911059400195254443 : Real) / (500000000000000000 : Real))| <= ((4443768387851912201 : Real) / (50000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((3 : Real) / (5 : Real)) ((911059400195254443 : Real) / (500000000000000000 : Real)) ((4443768387851912201 : Real) / (50000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_7 :
    |Real.exp ((19 : Real) / (40 : Real)) - ((402003549371445723 : Real) / (250000000000000000 : Real))| <= ((13222984690209957 : Real) / (80000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((19 : Real) / (40 : Real)) ((402003549371445723 : Real) / (250000000000000000 : Real)) ((13222984690209957 : Real) / (80000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_8 :
    |Real.exp ((7 : Real) / (20 : Real)) - ((11086465223384823 : Real) / (7812500000000000 : Real))| <= ((9572960443378973743 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((7 : Real) / (20 : Real)) ((11086465223384823 : Real) / (7812500000000000 : Real)) ((9572960443378973743 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_9 :
    |Real.exp ((9 : Real) / (40 : Real)) - ((39135084880995763 : Real) / (31250000000000000 : Real))| <= ((7104996091204212537 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((9 : Real) / (40 : Real)) ((39135084880995763 : Real) / (31250000000000000 : Real)) ((7104996091204212537 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_10 :
    |Real.exp ((1 : Real) / (10 : Real)) - ((34536591189863991 : Real) / (31250000000000000 : Real))| <= ((1089853653258725631 : Real) / (12500000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((1 : Real) / (10 : Real)) ((34536591189863991 : Real) / (31250000000000000 : Real)) ((1089853653258725631 : Real) / (12500000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_11 :
    |Real.exp ((-1 : Real) / (40 : Real)) - ((9753099120283326151 : Real) / (10000000000000000000 : Real))| <= ((343134932153377529 : Real) / (5000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-1 : Real) / (40 : Real)) ((9753099120283326151 : Real) / (10000000000000000000 : Real)) ((343134932153377529 : Real) / (5000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_12 :
    |Real.exp ((-3 : Real) / (20 : Real)) - ((53794248526566113 : Real) / (62500000000000000 : Real))| <= ((361451688263310551 : Real) / (50000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-3 : Real) / (20 : Real)) ((53794248526566113 : Real) / (62500000000000000 : Real)) ((361451688263310551 : Real) / (50000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_13 :
    |Real.exp ((-11 : Real) / (40 : Real)) - ((3797860616124842381 : Real) / (5000000000000000000 : Real))| <= ((2372223174259445377 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-11 : Real) / (40 : Real)) ((3797860616124842381 : Real) / (5000000000000000000 : Real)) ((2372223174259445377 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_14 :
    |Real.exp ((-2 : Real) / (5 : Real)) - ((268128018414255731 : Real) / (400000000000000000 : Real))| <= ((1337778355080387119 : Real) / (50000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-2 : Real) / (5 : Real)) ((268128018414255731 : Real) / (400000000000000000 : Real)) ((1337778355080387119 : Real) / (50000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_15 :
    |Real.exp ((-21 : Real) / (40 : Real)) - ((5915553643668151063 : Real) / (10000000000000000000 : Real))| <= ((2444297406964237139 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-21 : Real) / (40 : Real)) ((5915553643668151063 : Real) / (10000000000000000000 : Real)) ((2444297406964237139 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_16 :
    |Real.exp ((-13 : Real) / (20 : Real)) - ((5220457767610160449 : Real) / (10000000000000000000 : Real))| <= ((4789460814199831567 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-13 : Real) / (20 : Real)) ((5220457767610160449 : Real) / (10000000000000000000 : Real)) ((4789460814199831567 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_17 :
    |Real.exp ((-31 : Real) / (40 : Real)) - ((4607037809989658061 : Real) / (10000000000000000000 : Real))| <= ((222734962881832437 : Real) / (12500000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-31 : Real) / (40 : Real)) ((4607037809989658061 : Real) / (10000000000000000000 : Real)) ((222734962881832437 : Real) / (12500000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_18 :
    |Real.exp ((-9 : Real) / (10 : Real)) - ((4065696597405991097 : Real) / (10000000000000000000 : Real))| <= ((237669084816679441 : Real) / (20000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-9 : Real) / (10 : Real)) ((4065696597405991097 : Real) / (10000000000000000000 : Real)) ((237669084816679441 : Real) / (20000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_19 :
    |Real.exp ((-41 : Real) / (40 : Real)) - ((717592930811903229 : Real) / (2000000000000000000 : Real))| <= ((2061020261114686949 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-41 : Real) / (40 : Real)) ((717592930811903229 : Real) / (2000000000000000000 : Real)) ((2061020261114686949 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_20 :
    |Real.exp ((-23 : Real) / (20 : Real)) - ((1583183846895266089 : Real) / (5000000000000000000 : Real))| <= ((1821019995425054681 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-23 : Real) / (20 : Real)) ((1583183846895266089 : Real) / (5000000000000000000 : Real)) ((1821019995425054681 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_21 :
    |Real.exp ((-51 : Real) / (40 : Real)) - ((2794309682214073387 : Real) / (10000000000000000000 : Real))| <= ((1147938299775597707 : Real) / (100000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-51 : Real) / (40 : Real)) ((2794309682214073387 : Real) / (10000000000000000000 : Real)) ((1147938299775597707 : Real) / (100000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

private lemma qrow_bound_1_22 :
    |Real.exp ((-7 : Real) / (5 : Real)) - ((19265387807938007 : Real) / (78125000000000000 : Real))| <= ((461202775249444941 : Real) / (20000000000000000000000000000000000 : Real)) := by
  exact exp_abs_sub_le_of_half_taylor
    ((-7 : Real) / (5 : Real)) ((19265387807938007 : Real) / (78125000000000000 : Real)) ((461202775249444941 : Real) / (20000000000000000000000000000000000 : Real)) (n := 23)
    (by norm_num)
    (by norm_num)
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])
    (by norm_num [qrowTaylorS, qrowTaylorE])

/-- Imported primary `k=11` Q rows enclose the active analytic boundary rows. -/
theorem primaryK11QRadius_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticQ primaryK11Q primaryK11QRadius := by
  intro i j
  fin_cases i <;> fin_cases j
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_0
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_1
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_2
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_3
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_4
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_5
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_6
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_7
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_8
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_9
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_10
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_11
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_12
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_13
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_14
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_15
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_16
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_17
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_18
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_19
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_20
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_21
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_22
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_0
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_1
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_2
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_3
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_4
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_5
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_6
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_7
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_8
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_9
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_10
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_11
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_12
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_13
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_14
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_15
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_16
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_17
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_18
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_19
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_20
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_21
  · norm_num [CenteredCoeffDictionaryImport.primaryK11AnalyticQ_zero,
      CenteredCoeffDictionaryImport.primaryK11AnalyticQ_one,
      primaryK11Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, primaryK11Q, primaryK11QRat,
      primaryK11QEntryRat, primaryK11QRadius, primaryK11QRadiusRat,
      primaryK11QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_22

/-- Imported control `k=9` Q rows enclose the active analytic boundary rows. -/
theorem controlK9QRadius_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticQ controlK9Q controlK9QRadius := by
  intro i j
  fin_cases i <;> fin_cases j
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_0
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_1
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_2
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_3
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_4
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_5
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_6
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_7
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_8
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_9
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_10
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_11
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_12
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_13
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_14
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_15
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_16
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_17
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_18
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_19
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_20
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_21
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_0_22
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_0
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_1
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_2
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_3
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_4
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_5
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_6
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_7
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_8
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_9
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_10
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_11
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_12
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_13
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_14
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_15
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_16
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_17
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_18
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_19
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_20
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_21
  · norm_num [CenteredCoeffDictionaryImport.controlK9AnalyticQ_zero,
      CenteredCoeffDictionaryImport.controlK9AnalyticQ_one,
      controlK9Center, activeL3Ell030Delta025Center,
      activeL3Ell030Delta025CenterRatEntry, controlK9Q, controlK9QRat,
      controlK9QEntryRat, controlK9QRadius, controlK9QRadiusRat,
      controlK9QRadiusEntryRat]
    simpa [neg_div] using qrow_bound_1_22

end CenteredCoeffQRowImport
end PSDpd
end Q3
