import Q3.Axioms
import Q3.Proofs.Params_Critical
import Q3.Proofs.A3_Floor_Bounds
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.Bmin_1826
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatProof
import Q3.Proofs.PrimeTerm_PathB_legacy_provider

set_option linter.mathlibStandardSet false

open scoped Real

noncomputable section

namespace Q3

open Q3.Proofs.PrimeCert

/-!
Tau-0 B-range gate for Path B mainline.

This module keeps the public tau-0 gate API and discharges it by
specializing the stable all-τ Path B contract to `τ = 0` on the
certified B-range.
-/

/-- Tau-0 Path B gate on the certified B-range. -/
def PrimeTermPathBTcriticalTau0Brange : Prop :=
  ∀ B : ℝ, B_min ≤ B → B ≤ prime_cert_B_max →
    prime_term (fun ξ => phi_shift B t_critical 0 ξ) ≤
      arch_term (fun ξ => phi_shift B t_critical 0 ξ)

/-- Slack route (prime side): uniform quarter-bound on the certified τ=0 B-range. -/
def PrimeTermTau0BrangePrimeQuarter : Prop :=
  ∀ B : ℝ, B_min ≤ B → B ≤ prime_cert_B_max →
    prime_term (fun ξ => phi_shift B t_critical 0 ξ) ≤ c_star / 4

/-- Slack route (arch side): floor bound on the certified τ=0 B-range. -/
def PrimeTermTau0BrangeArchFloor : Prop :=
  ∀ B : ℝ, B_min ≤ B → B ≤ prime_cert_B_max →
    c_star ≤ arch_term (fun ξ => phi_shift B t_critical 0 ξ)

/-- Slack route (arch side): quarter-bound on the certified τ=0 B-range. -/
def PrimeTermTau0BrangeArchQuarter : Prop :=
  ∀ B : ℝ, B_min ≤ B → B ≤ prime_cert_B_max →
    c_star / 4 ≤ arch_term (fun ξ => phi_shift B t_critical 0 ξ)

/-- Pure slack composition for τ=0 gate:
`prime_term ≤ c_star/4` and `c_star ≤ arch_term` imply `prime_term ≤ arch_term`. -/
theorem prime_term_pathB_tcritical_tau0_brange_of_slack
    (hPrimeQuarter : PrimeTermTau0BrangePrimeQuarter)
    (hArchFloor : PrimeTermTau0BrangeArchFloor) :
    PrimeTermPathBTcriticalTau0Brange := by
  intro B hBmin hBmax
  have hprime : prime_term (fun ξ => phi_shift B t_critical 0 ξ) ≤ c_star / 4 :=
    hPrimeQuarter B hBmin hBmax
  have harch_floor : c_star ≤ arch_term (fun ξ => phi_shift B t_critical 0 ξ) :=
    hArchFloor B hBmin hBmax
  have hquarter_le_arch :
      c_star / 4 ≤ arch_term (fun ξ => phi_shift B t_critical 0 ξ) := by
    have hquarter_le_cstar : c_star / 4 ≤ c_star := by
      nlinarith [c_star_pos]
    exact le_trans hquarter_le_cstar harch_floor
  exact le_trans hprime hquarter_le_arch

/-- Pure quarter-slack composition for τ=0 gate:
`prime_term ≤ c_star/4` and `c_star/4 ≤ arch_term` imply `prime_term ≤ arch_term`. -/
theorem prime_term_pathB_tcritical_tau0_brange_of_quarter_slack
    (hPrimeQuarter : PrimeTermTau0BrangePrimeQuarter)
    (hArchQuarter : PrimeTermTau0BrangeArchQuarter) :
    PrimeTermPathBTcriticalTau0Brange := by
  intro B hBmin hBmax
  exact le_trans
    (hPrimeQuarter B hBmin hBmax)
    (hArchQuarter B hBmin hBmax)

/-- Certified arch-floor on the full τ=0 B-range, from:
`B=B_min` arch certificate + heat-Lipschitz transport. -/
theorem prime_term_tau0_brange_arch_floor_from_heat :
    PrimeTermTau0BrangeArchFloor := by
  intro B hBmin hBmax
  have hBmax_ge : B_min ≤ prime_cert_B_max := by
    norm_num [B_min, prime_cert_B_max]
  have hBIcc : B ∈ Set.Icc B_min prime_cert_B_max := ⟨hBmin, hBmax⟩
  have hBminIcc : B_min ∈ Set.Icc B_min prime_cert_B_max := ⟨le_rfl, hBmax_ge⟩
  have hLip :
      |arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B) -
        arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B_min)| ≤
        (Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B - B_min| := by
    exact Q3.Proofs.PrimeCert.arch_term_Lipschitz_heat
      (B1 := B) (B2 := B_min) hBIcc hBminIcc
      Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data
  have hdist : |B - B_min| ≤ prime_cert_B_max - B_min := by
    have hsub_nonneg : 0 ≤ B - B_min := sub_nonneg.mpr hBmin
    have hsub_le : B - B_min ≤ prime_cert_B_max - B_min := sub_le_sub_right hBmax B_min
    simpa [abs_of_nonneg hsub_nonneg] using hsub_le
  have hC_nonneg : 0 ≤ Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw / (B_min ^ 2) := by
    have hnum : 0 ≤ Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw := by
      norm_num [Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw]
    have hden : 0 ≤ B_min ^ 2 := by nlinarith
    exact div_nonneg hnum hden
  have hLip' :
      |arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B) -
        arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B_min)| ≤
        (Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw / (B_min ^ 2)) *
          (prime_cert_B_max - B_min) := by
    exact le_trans hLip (mul_le_mul_of_nonneg_left hdist hC_nonneg)
  have hBmin_cert :
      Q3.Proofs.PrimeCert.prime_cert_arch_lb ≤
        arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B_min) :=
    Q3.Proofs.PrimeCert.arch_term_cert_on_Bmin_tau0
  have harch_transport :
      arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B_min) -
          (Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw / (B_min ^ 2)) *
            (prime_cert_B_max - B_min) ≤
        arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B) := by
    have hleft :
        -(Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw / (B_min ^ 2) *
            (prime_cert_B_max - B_min)) ≤
          arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B) -
            arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B_min) := by
      have hAbs := abs_sub_le_iff.mp hLip'
      nlinarith [hAbs.2]
    nlinarith
  have hnum :
      c_star ≤
        Q3.Proofs.PrimeCert.prime_cert_arch_lb -
          (Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw / (B_min ^ 2)) *
            (prime_cert_B_max - B_min) := by
    norm_num [c_star, Q3.Proofs.PrimeCert.prime_cert_arch_lb,
      Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw, B_min, prime_cert_B_max]
  have hbase :
      c_star ≤
        arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B_min) -
          (Q3.Proofs.PrimeCert.prime_cert_L_arch_heat_raw / (B_min ^ 2)) *
            (prime_cert_B_max - B_min) := by
    nlinarith [hnum, hBmin_cert]
  have hgoal :
      c_star ≤ arch_term (Q3.Proofs.PrimeCert.phi_shift_critical_tau0 B) := by
    exact le_trans hbase harch_transport
  simpa [Q3.Proofs.PrimeCert.phi_shift_critical_tau0] using hgoal

/-- Prime-quarter on τ=0 brange via the current Path B math-facing axiom.
This isolates the remaining debt to a single prime-side obligation. -/
theorem prime_term_tau0_brange_prime_quarter_from_legacy :
    PrimeTermTau0BrangePrimeQuarter := by
  intro B hBmin _hBmax
  have hBmin_pos : (0 : ℝ) < B_min := by
    norm_num [B_min]
  have hB : B > 0 := by
    linarith
  let K0 : ℝ := max 1 B
  have hK0 : K0 ≥ 1 := by
    exact le_max_left (1 : ℝ) B
  have hτB0 : |(0 : ℝ)| + B ≤ K0 := by
    have hB_le : B ≤ K0 := by
      simpa [K0] using (le_max_right (1 : ℝ) B)
    simpa using hB_le
  exact Q3.prime_term_tcritical_le_cstar_quarter_mathan K0 B 0 hK0 hB hτB0

/-- Arch-quarter on τ=0 brange via the current Path B math-facing axiom.
This isolates the remaining debt to a single arch-side obligation. -/
theorem prime_term_tau0_brange_arch_quarter_from_legacy :
    PrimeTermTau0BrangeArchQuarter := by
  intro B hBmin _hBmax
  have hBmin_pos : (0 : ℝ) < B_min := by
    norm_num [B_min]
  have hB : B > 0 := by
    linarith
  let K0 : ℝ := max 1 B
  have hK0 : K0 ≥ 1 := by
    exact le_max_left (1 : ℝ) B
  have hτB0 : |(0 : ℝ)| + B ≤ K0 := by
    have hB_le : B ≤ K0 := by
      simpa [K0] using (le_max_right (1 : ℝ) B)
    simpa using hB_le
  exact Q3.cstar_quarter_le_arch_term_tcritical_mathan K0 B 0 hK0 hB hτB0

/-- Tau-0 B-range gate by specializing any Path B `t_critical` contract. -/
theorem prime_term_pathB_tcritical_tau0_brange_of_pathB
    (hPathB : PrimeTermPathBTcritical) :
    PrimeTermPathBTcriticalTau0Brange := by
  intro B hBmin _hBmax
  have hBmin_pos : (0 : ℝ) < B_min := by
    norm_num [B_min]
  have hB : B > 0 := by
    linarith
  let K0 : ℝ := max 1 B
  have hK0 : K0 ≥ 1 := by
    exact le_max_left (1 : ℝ) B
  have hτB0 : |(0 : ℝ)| + B ≤ K0 := by
    have hB_le : B ≤ K0 := by
      simpa [K0] using (le_max_right (1 : ℝ) B)
    simpa using hB_le
  simpa using hPathB K0 B 0 hK0 hB hτB0

/-- Closure point for the analytic route:
once the τ=0 prime-quarter obligation is proved as a theorem, the full τ=0
B-range gate follows without any legacy provider wiring. -/
theorem prime_term_pathB_tcritical_tau0_brange_of_prime_quarter
    (hPrimeQuarter : PrimeTermTau0BrangePrimeQuarter) :
    PrimeTermPathBTcriticalTau0Brange :=
  prime_term_pathB_tcritical_tau0_brange_of_slack
    hPrimeQuarter
    prime_term_tau0_brange_arch_floor_from_heat

/-- Tau-0 B-range gate by direct quarter-route composition.
This keeps the mainline contract on the narrowed τ=0 brange interface. -/
theorem prime_term_pathB_tcritical_tau0_brange_analytic :
    PrimeTermPathBTcriticalTau0Brange :=
  prime_term_pathB_tcritical_tau0_brange_of_quarter_slack
    prime_term_tau0_brange_prime_quarter_from_legacy
    prime_term_tau0_brange_arch_quarter_from_legacy

/-- Canonical tau-0 Path B gate provider for mainline routing. -/
theorem prime_term_pathB_tcritical_tau0_brange_thm :
    PrimeTermPathBTcriticalTau0Brange :=
  prime_term_pathB_tcritical_tau0_brange_analytic

end Q3
