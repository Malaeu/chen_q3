# Drift report M1-M4 (A3 symbol mismatch)

Short goal: capture the exact mismatch between the paper contract and current Lean wiring.

## M1) a_star vs P_A - DRIFT CONFIRMED

Problem:
- Public A3 bridge still uses `a_star` with sampling Toeplitz.

Wrong locations (sampling symbol):
- `full/q3.lean.aristotle/Q3/Axioms.lean`:
  `A3_bridge_axiom`, `A3_bridge_uniform`, `A3_bridge_rayleigh_axiom`,
  `A3_bridge_data`, `A3_bridge_data_uniform`, `A3_bridge_data_rayleigh`
- `full/q3.lean.aristotle/Q3/Proofs/A3_bridge_rayleigh_first.lean`:
  `h_rayleigh_lower_bound` uses `ToeplitzMatrix (2*M+1) a_star`

Correct formulation exists:
- `full/q3.lean.aristotle/Q3/Proofs/P_A_Toeplitz_bridge.lean`
  `A3_bridge_data_rayleigh_Fourier` uses Fourier Toeplitz and `P_A`
- `full/q3.lean.aristotle/Q3/Proofs/Rayleigh_Fourier.lean`
  defines `ToeplitzMatrix_Fourier_real` and `rayleigh_lower_bound_real`

## M2) Sampling vs Fourier - DRIFT CONFIRMED

Old (wrong for A3 chain):
- `ToeplitzMatrix ... a_star` (sampling form)

New (correct):
- `RayleighFourier.ToeplitzMatrix_Fourier_real ... (P_A B_min t_sym)`

## M3) Prime operator - OK

Correct (compression form):
- `full/q3.lean.aristotle/Q3/Basic/Defs.lean`
  `T_P_comp_real` uses `w_Q * fejer_heat_window`

Note:
- Deprecated A3 axioms still use `w_RKHS` + Gaussian kernel.

## M4) Parameters - OK (split across files)

- `t_sym` is fixed in `full/q3.lean.aristotle/A3_Floor_Main.lean`
- `t_rkhs_cap` and `rho_one` are in
  `full/q3.lean.aristotle/Q3/Proofs/A3_bridge_rayleigh_first.lean`

## Canonical correct definitions (for Proshka)

From `Q3/Proofs/P_A_Toeplitz_bridge.lean`:
```lean
def A3_bridge_data_rayleigh_Fourier (K : ℝ) : Prop :=
  ∀ (hK : K ≥ 1) [Fintype (Q3.Nodes K)],
    ∃ t > 0, ∀ M : ℕ,
      ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
        Q3.RayleighQuotient
            (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym) -
             Q3.T_P_comp_real K K t M) v
          ≥ Q3.c_star / 4
```

Wiring theorem (already present):
```lean
theorem A3_bridge_rayleigh_Fourier (K : ℝ) (hK : K > 0) :
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K := by
  apply Q3.Proofs.P_A_Bridge.A3_bridge_rayleigh_from_weight_sum_P_A K
  intro _inst
  exact Q3.Proofs.weight_sum_le_rho_one K K hK
```

## Minimal fix set

1) Keep old sampling A3 data as deprecated, but remove it from public chain.
2) Publicly expose `A3_bridge_data_rayleigh_Fourier` and wire `A3_bridge` to it.
3) Keep `A3_bridge_rayleigh_first.lean` deprecated (do not import in main path).

## Quick checks

- Sampling drift:
  `rg -n "ToeplitzMatrix .* a_star" full/q3.lean.aristotle/Q3`
- Wrong weights:
  `rg -n "w_RKHS" full/q3.lean.aristotle/Q3`
- Correct path exists:
  `rg -n "ToeplitzMatrix_Fourier_real.*P_A" full/q3.lean.aristotle/Q3`
