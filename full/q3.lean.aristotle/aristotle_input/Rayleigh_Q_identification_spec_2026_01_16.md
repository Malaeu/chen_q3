# Spec: Rayleigh-Q identification (Theorem 3.3)

## Goal
Close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` by proving the Rayleigh-Q
identification for the Fejer-heat window.

Target statement (Lean sketch):
```
noncomputable def basis0 (M : ℕ) : Fin (2 * M + 1) → ℝ :=
  let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩
  fun i => if i = i0 then (1 : ℝ) else 0

/-- Rayleigh-Q identification (Theorem 3.3). -/
theorem rayleigh_Q_identification
    (B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes B)] :
  (2 * M + 1 : ℝ) *
    Q3.RayleighQuotient
      (Q3.Proofs.RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t)
        - Q3.T_P_comp_real B B t M)
      (basis0 M)
  = Q3.Q (fun ξ => Q3.fejer_heat_window B t ξ) := by
  -- proof
  sorry
```

## Contract checks (must hold)
- Symbol: `P_A` (periodized, windowed), not `a_star`.
- Toeplitz: Fourier/Rayleigh (`ToeplitzMatrix_Fourier_real`), not sampling.
- Prime operator: compression `T_P_comp_real` with `w_Q`, not direct-indexed `T_P`.
- Keep `t_sym` and `t_rkhs` separate.

## Lemma chain (suggested)
B1) `basis0_norm_sq` and `basis0_ne_zero`.
B2) `rayleigh_basis0_eq_diag`:
```
(2*M+1) * RayleighQuotient A (basis0 M) = A i0 i0
```
B3) `toeplitz_diag_eq_integral`:
```
ToeplitzMatrix_Fourier_real (2*M+1) (P_A B t) i0 i0
  = ∫ theta in (-1/2)..(1/2), P_A B t theta
```
B4) `tpcomp_diag_eq_sum`:
```
T_P_comp_real B B t M i0 i0
  = (1/(2*M+1)) * ∑ n : Nodes B, w_Q n * fejer_heat_window B t (xi_n n)
```
Use `prime_vec_norm` / `prime_vec_norm_sq_sum` from `Q3/Basic/Defs.lean`.
B5) `periodized_integral_eq_arch`:
```
∫_{-1/2}^{1/2} P_A = arch_term (fun xi => fejer_heat_window B t xi)
```
B6) `prime_term_eq_nodes`:
```
prime_term (fun xi => fejer_heat_window B t xi)
  = ∑ n : Nodes B, w_Q n * fejer_heat_window B t (xi_n n)
```

## Assembly
- Use B2 to reduce Rayleigh quotient to a diagonal entry.
- Split diagonal of `(A - B)`.
- Apply B3 and B4.
- Rewrite with B5 and B6.
- Unfold `Q = arch_term - prime_term` and finish by `ring_nf`.

## Risk notes
- Normalization: if your `RayleighQuotient` definition is slightly different,
  the `(2*M+1)` factor may shift. Check once before wiring.
- Integral domain: stick to `(-1/2)..(1/2)` consistently.

## DO NOT DO
- Do not use sampling Toeplitz.
- Do not replace `P_A` by `a_star`.
- Do not use direct-indexed `T_P`.
