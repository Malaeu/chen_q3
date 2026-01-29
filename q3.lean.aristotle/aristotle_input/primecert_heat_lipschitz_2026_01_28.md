# PrimeCert heat Lipschitz (t_critical, tau = 0)

**Target file:** `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatProof.lean`

We need to fill the three `sorry` blocks in that file.  
Please **do not** introduce `exact?` or new `sorry`. Keep the proof local and
reuse existing lemmas.

## Context / imports

The file already imports:
- `Q3.Proofs.PrimeCert.Brange_Lipschitz_Analytic` (for `phi_shift_lipschitz_B_exp`)
- `Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatScaffold` (for `phi_shift_critical_tau0`, `margin_tau0`)
- `Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28` (numeric constants)

Definitions used:
- `arch_term (Φ) := ∫ ξ, a_star ξ * Φ ξ`
- `prime_term (Φ) := ∑' n, w_Q n * Φ (xi_n n)`
- `phi_shift_critical_tau0 B ξ := phi_shift B t_critical 0 ξ`
- `heat_weight ξ := exp(-4π² t_critical ξ²) * |ξ|`
- `phi_shift_lipschitz_B_exp` (pointwise bound)

## Goal 1 (arch term heat Lipschitz)

Fill lemma:
```
lemma arch_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight ξ ≤ prime_cert_L_arch_heat_raw) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2|
```

**Idea:**  
Use `phi_shift_lipschitz_B_exp` to bound  
`|phi_shift B1 t_critical 0 ξ - phi_shift B2 t_critical 0 ξ|`
by `heat_weight ξ * |B1 - B2| / (B_min^2)`.  
Then apply `|∫ f| ≤ ∫ |f|` and the integrand bound with `|a_star ξ|`.  
Finally use the numeric hypothesis `h_arch_heat`.

## Goal 2 (prime term heat Lipschitz)

Fill lemma:
```
lemma prime_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight (xi_n n) ≤ prime_cert_L_prime_heat_raw) :
    |prime_term (phi_shift_critical_tau0 B1) -
      prime_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_prime_heat_raw / (B_min ^ 2)) * |B1 - B2|
```

**Idea:**  
Expand `prime_term` as `tsum`, use triangle inequality for `tsum`,
and apply the pointwise bound from `phi_shift_lipschitz_B_exp` at `xi_n n`.  
Use `w_Q_nonneg` (from `Q_Lipschitz_prime_bridge`) to move abs inside.  
Then factor `|B1 - B2| / (B_min^2)` and use `h_prime_heat`.

## Goal 3 (combine)

Fill lemma:
```
lemma margin_Lipschitz_heat_of_bounds
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight ξ ≤ prime_cert_L_arch_heat_raw)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight (xi_n n) ≤ prime_cert_L_prime_heat_raw)
    (h_total :
      (prime_cert_L_arch_heat_raw + prime_cert_L_prime_heat_raw) / (B_min ^ 2) ≤
        prime_cert_L_total_heat_ub) :
    |margin_tau0 B1 - margin_tau0 B2| ≤
      prime_cert_L_total_heat_ub * |B1 - B2|
```

**Idea:**  
Use `arch_term_Lipschitz_heat` + `prime_term_Lipschitz_heat` and the triangle
inequality on `margin_tau0`. Then apply `h_total`.

---

Please keep proofs minimal and robust; prefer `simp`, `linarith`, `nlinarith` where appropriate.
