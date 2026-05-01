# Q3 PSD-pd Class 1 Shifted Cap Audit (2026-05-01)

Status: in progress

Placement:

- This belongs to the fallback corrected-cone route
  `A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2 -> LF-pd -> G6`.
- It does not pivot the active control plane away from the primary
  `H-bridge / PO3-square.2d3` frontier.

## Question

Can the current centered Fejer x heat/RKHS prime cap be expanded to the first
honest square-class enlargement:

```math
\text{shifted Fejer x heat autocorrelations}
```

without losing the operator inequality

```math
P_{\mathrm{prime}}\preceq \rho A_{\mathrm{arch}},
\qquad \rho<1?
```

This is the first real test for `Q3_PSDpd_Expansion`.

## Local evidence

The repository already has shifted scalar/basis0 facts.

In `Q3/Proofs/Rayleigh_Q_identification.lean`:

- `T_P_comp_real_shift` defines the shifted real prime compression.
- `prime_rayleigh_eq_shift` identifies the shifted prime Rayleigh quotient on
  `basis0`.
- `prime_term_eq_nodes_sum_shift` and `rayleigh_Q_eq_Q_shift` connect the
  shifted Rayleigh formula back to the scalar shifted Q-functional.

In `Q3/Proofs/RKHS_cap_rayleigh.lean`:

- `rho_oneK K := exp(8*pi^2*t_rkhs_cap*K^2) * rho_one`.
- `weight_sum_le_rho_oneK` gives a K-dependent shifted weight-sum bound.
- `prime_rayleigh_shift_le_rho_oneK` proves the shifted prime Rayleigh cap only
  for `basis0`, with the explicit `(2*M+1)` prime normalization factor.
- `prime_term_phi_shift_le_rho_oneK` gives the corresponding scalar shifted
  prime-term cap.

The unshifted full-vector route also exists:

- `T_P_comp_real_opNorm_le_weight_sum`;
- `rkhs_cap_rayleigh_of_weight_sum`.

But the shifted full-vector analog is not currently present.

## Verdict

The current shifted lemmas do **not** close Class 1.

They prove that a single shifted scalar window, tested against the constant
Rayleigh vector `basis0`, has a K-dependent cap.  That is useful, but it is not
the square-space statement needed by `PSD-pd`.

Class 1 needs a full-vector/operator statement for finite shifted packet
families:

```math
v^* P_{\mathrm{prime,shift}} v
\le
\rho\, v^* A_{\mathrm{arch,shift}} v
\qquad\text{for all }v.
```

Equivalently, the prime sampling measure must be Carleson-small for the shifted
RKHS square class, not merely for the `basis0` scalar window.

## Normalization checkpoint

The existing shifted basis0 theorem has the correct warning built in:

```math
(2M+1)\,\operatorname{RQ}(T_P^{\mathrm{shift}},\mathrm{basis0})
=
\sum_n w_Q(n)\,\phi_{\mathrm{shift}}(\xi_n).
```

So any Class 1 theorem must keep the same convention:

- either use the normalized `T_P^{Ray}` and carry `(2M+1)` on the prime term;
- or redefine the prime block as the unnormalized Weil block and state that
  convention explicitly.

Do not mix these two forms.

## Next Lean target

The smallest useful theorem packet is the shifted analog of the existing
unshifted op-norm chain:

1. `T_P_comp_real_shift_entry_abs_le_weight_sum`
2. `T_P_comp_real_shift_row_sum_le_weight_sum`
3. `T_P_comp_real_shift_opNorm_le_weight_sum`
4. `shifted_rkhs_cap_rayleigh_of_weight_sum`

Expected shape:

```lean
lemma T_P_comp_real_shift_opNorm_le_weight_sum
    (K B t tau : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    ‖Q3.T_P_comp_real_shift K B t tau M‖ ≤
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n)) : ℂ)‖
```

Then:

```lean
lemma shifted_rkhs_cap_rayleigh_of_weight_sum
    (K B t tau rho : ℝ) [Fintype (Q3.Nodes K)]
    (h_weight_sum :
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.phi_shift B t tau (Q3.xi_n n)) : ℂ)‖ ≤ rho) :
    ∀ M v, v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t tau M) v ≤ rho
```

The algebraic consumer is already available in
`Q3/Proofs/PSD_FormAlgebra.lean`.

## Scale obstruction

The shifted cap currently lands at

```math
\rho_{\mathrm{oneK}}(K)
=
\exp(8\pi^2 t_{\mathrm{rkhs\_cap}}K^2)\rho_{\mathrm{one}}.
```

This is not automatically `<1`, and it is not automatically below the relevant
Archimedean floor.  Therefore the real Class 1 question has two parts:

1. prove the shifted full-vector cap;
2. prove the cap stays below the floor on the compact/scale regime used in the
   PSD-pd exhaustion.

If the second part fails as `K` or the scale range expands, then centered Q3
constants cannot close `PSD-pd` through shifted/mixed-scale density without a
new ingredient.

## Failure criterion

Class 1 fails with current constants if either:

- only the `basis0` shifted cap is available and no full-vector operator cap can
  be proved; or
- the full-vector cap exists but the best available bound grows past the
  Archimedean floor before reaching a dense shifted/mixed-scale square class.

In that case, Q3 remains a finite companion/checker layer, not a completed
Weil-square proof.

## Next action

Do not jump to mixed scales yet.

First build or request the shifted op-norm theorem packet above.  If it compiles
cleanly, instantiate the finite PSD algebra:

```math
\text{arch floor} - \text{shifted prime cap} \ge 0
```

on the Class 1 shifted packet block.

## Implementation audit (same session)

An initial Lean patch was drafted with the intended theorem names:

- `T_P_comp_real_shift_opNorm_le_weight_sum`;
- `shifted_rkhs_cap_rayleigh_of_weight_sum`.

The draft copied the existing unshifted Schur/row-sum proof pattern with
`fejer_heat_window` replaced by `phi_shift`.

It was **not integrated**.  The reason was not a local proof failure; targeted
checks stalled while reading the heavy import layer around `Q3.Basic.Defs`, and
even the already-existing `T_P_comp_utils.lean` showed the same behavior in
this session.  Under the project workflow, unverified Lean must not enter the
mainline.

Safe next implementation path:

1. move only the lightweight shifted definitions
   `phi_shift`, `T_P_comp_shift`, `T_P_comp_real_shift` into a small import
   layer;
2. keep `g_shift`, `P_A_shift`, and shifted periodization proofs in the
   heavier `ShiftedWindows`/`Rayleigh_Q_identification` layer;
3. verify that lightweight layer first;
4. only then add the shifted Schur/op-norm proof packet.

This is an import-architecture issue, not a change to the mathematical target.
