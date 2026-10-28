# Parity gap table on the literal CCM matrix (THETAGRADE Q2 first fact), 2026-10-28

DIAGNOSTIC_NEVER_A_PROOF. 15 cells m = 2..16, m = N, literal `matrix_K` and selected reference row from
`../fokas_k_sign_2026-09-25/`. Script `parity_gap_table.py`; raw rows `table_dps120.jsonl`, `table_dps170.jsonl`.
Precision check: dps 120 and dps 170 agree in all 20 printed digits on every cell.
Cross-check: alpha_4, alpha_8, alpha_13 = 0.0309 / 0.0553 / 0.0605 match PAPER_CHAIN G3 diagnostics 0.03089 / 0.05534 / 0.06052.

| m | λ_even | λ_odd | D_m | λ_odd/λ_even | ‖r_m‖ | δ_m | α_m | (a_m−λ₁)/D_m | cos²(ξ,η)/λ₁ |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 3.06e-3 | 0.126 | 0.123 | 41 | 1.99e-2 | 0.122 | 0.020 | 0.0032 | 1.50 |
| 4 | 1.70e-9 | 3.03e-7 | 3.02e-7 | 179 | 5.29e-5 | 2.23e-7 | 0.031 | 0.26 | 1.59 |
| 5 | 3.55e-12 | 1.03e-9 | 1.02e-9 | 288 | 3.11e-5 | −7.81e-9 | 0.043 | 8.7 | 1.61 |
| 8 | 1.02e-19 | 3.34e-17 | 3.33e-17 | 326 | 2.97e-6 | −1.14e-11 | 0.055 | 3.4e5 | 1.31 |
| 12 | 6.79e-29 | 4.15e-26 | 4.14e-26 | 611 | 4.98e-9 | −6.32e-17 | 0.060 | 1.5e9 | 1.17 |
| 16 | 5.46e-38 | 6.85e-35 | 6.85e-35 | 1256 | 7.70e-10 | −7.35e-19 | 0.058 | 1.1e16 | 1.29 |
All 15 cells are in the jsonl files; the rows shown follow the same trend.

## Findings
1. Parity: on all 15 cells the ground state is simple and even, and λ₂ = λ_odd, so the simplicity gap equals D_m > 0.
   The relative gap λ_odd/λ_even grows from 41 to 1256. No sign of a parity collapse. Observer prediction "D_m > 0 on all cells" (0.85): hit.
2. Residual side of G1 fails on cells 5..16: δ_m < 0. Mechanism (exact): q_m is even (parity defect 0), so every odd y is orthogonal to q_m and
   δ_m ≤ λ_odd − a_m. Here a_m − λ₁ exceeds D_m by 8.7 (m=5) up to 1.1e16 (m=16), so a_m > λ_odd and δ_m < 0.
   With a = a_m, the literal odd floor hoddEv (λ_odd − a_m ≥ β₀ > 0) fails on the same cells.
3. Cause: α_m does not decay; it sits at 0.055–0.060 for m ≥ 8. The selected row is not close to the ground state, and a_m carries its weight on high eigenvalues.
   So the residual part of G1 is the tracking problem (G3) in another form, and it needs far more than a polynomial rate: a_m − λ₁ < D_m.
4. The ratio D_m/‖r_m‖ collapses (6.2 → 8.9e-26). This is NOT a parity collapse: ‖r_m‖ measures the distance of q_m from the ground state.
   The observer's branch wording ("D/r falls ⇒ parity collapse") was a poor discriminator; withdrawn.
5. Symptom: cos²(ξ, η)/λ₁ stays between 1.17 and 1.85 on all cells. So η·ξ ≍ √λ_min: the overlap of the ground state with the constant vector
   is tied to λ_min itself. Readings: (a) λ_min is the pole-term energy of a near-null vector of the remaining form; (b) coincidence of scales. Not explained.
6. Symptom: the selected row is conjugate-symmetric (z_{−n} = conj z_n) with an odd imaginary part 3.9e-3 (m=2) falling to 1.5e-41 (m=16). Source not checked.

## Consequence for G1 (split)
G1a — simple and even ground state: holds on all cells with a growing relative gap. Candidate for proof without zero input (Proshka's candidate B, parity-block Schur).
G1b — cellwise floor δ_m > 0 and ‖r_m‖/δ_m → 0 for the selected row, and hoddEv with a = a_m: false on cells 5..16.
Theorem shape to test: a_m > λ_min(K_m|odd) eventually. If proved, G1b and literal hoddEv are killed cofinally.
