import Q3.Proofs.PrimeCert.PrimeHeatMarginKernel
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28

/-!
Witness payload for the 2026-01-28 prime-heat margin certificate.

This intentionally exposes a single load-bearing witness constant for the
prime-heat branch, consumed by the margin kernel soundness route.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

def prime_heat_margin_cert_2026_01_28 : PrimeHeatMarginCert := by
  refine
    { source_path := prime_cert_heat_brange_source
      source_sha256 := prime_cert_heat_brange_sha256
      N := prime_cert_heat_N
      h_source_path := rfl
      h_source_sha256 := rfl
      h_N := rfl
      h_arch_heat := ?_
      h_prime_heat := ?_
      h_total_heat := ?_ }
  · simpa [brange_Icc, heat_weight] using prime_heat_bounds_arch_data
  ·
    simpa [heat_weight, mul_assoc, mul_left_comm, mul_comm, mul_ite, ite_mul]
      using prime_heat_bounds_prime_data
  · simpa using prime_heat_bounds_total

theorem prime_heat_margin_cert_2026_01_28_checked :
    checkPrimeHeatMarginCert prime_heat_margin_cert_2026_01_28 = true :=
  checkPrimeHeatMarginCert_true prime_heat_margin_cert_2026_01_28

end Q3.Proofs.PrimeCert
