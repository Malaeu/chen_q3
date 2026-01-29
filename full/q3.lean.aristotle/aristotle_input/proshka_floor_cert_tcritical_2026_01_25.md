# Proshka Request: floor certificate for P_A at t_critical (single-scale)
Timestamp: 2026-01-25 15:22

## Context
- We are in the single-scale branch with `t_critical = 3/20` and `B_min = 3`.
- `FloorGoal` requires:
  ```lean
  ∀ θ ∈ Set.Icc (-1/2) (1/2), c_star ≤ P_A B_min t_critical θ
  ```
- We already have a wrapper file:
  `Q3/Proofs/A3_Floor_Critical_Proof.lean` that reduces `FloorGoal` to the lemma
  `Q3.P_A_ge_c_star_at_t_critical` in `Q3/Proofs/Q_nonneg_t_critical.lean`.

## Task
Provide a Lean-ready proof (or minimal lemma decomposition) to replace the `sorry` in:

```lean
-- file: Q3/Proofs/Q_nonneg_t_critical.lean
lemma P_A_ge_c_star_at_t_critical (θ : ℝ) :
    P_A_critical B_min θ ≥ c_star := by
  -- TODO
```

You may choose one of these options:

### Option A (preferred, local certificate)
Prove a stronger local bound:
```lean
lemma P_A_ge_c_star_on_Icc_tcritical :
  ∀ θ ∈ Set.Icc (-1/2) (1/2), c_star ≤ P_A B_min t_critical θ := by
  -- certificate / interval arithmetic / discrete grid + modulus of continuity
```
Then derive `P_A_ge_c_star_at_t_critical` from periodicity of `P_A`.

### Option B (direct lemma)
Prove `P_A_ge_c_star_at_t_critical` directly with a periodicity step inside the proof.

## Constraints
- **Single-scale only**: use `t_critical`, no `t_sym` / two-scale bridges.
- **τ = 0** only.
- Provide a minimal list of supporting lemmas (2-3 max) if needed.
- If you use numeric bounds: specify the exact certificate step (interval arithmetic, grid + Lipschitz).
- No `sorry` / no `exact?`.

## Where to place results
- Primary lemma: `Q3/Proofs/Q_nonneg_t_critical.lean`
- If a helper file is needed: `Q3/Proofs/A3_Floor_Critical_Proof.lean`

## Useful facts already in repo
- `P_A` defined in `Q3/Proofs/A3_Floor_Main.lean`:
  `P_A (B t θ) = 2π * ∑' m, g B t (θ + m)` with `g = a * w` and `w = fejer_heat_window`.
- `P_A_shift` and `phi_shift` in `Q3/Proofs/ShiftedWindows.lean`.
- `P_A_critical` defined in `Q3/Proofs/Q_nonneg_t_critical.lean`:
  `P_A_critical B θ := P_A_shift B t_critical 0 θ`.
- `P_A_shift_tau_zero` rewriting lemma available (see `Q3/Proofs/A3_Floor_Critical_Proof.lean`).

## Deliverable
A Lean proof (or minimal lemma set) that closes `P_A_ge_c_star_at_t_critical`.
