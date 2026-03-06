# Sub-agent request: close the honest shifted-evenized `t_critical` node

## Goal

Do **not** try to prove the old scalar statement
`prime_term_le_at_t_critical_axiom` with the same signature unless you can
prove it honestly from the current repo context.

The active Lean/paper route only needs the correct shifted-evenized positivity
node. So the preferred target is:

1. `Q_phi_shift_pair_nonneg_t_critical`, or
2. `Q_Fejer_heat_atom_nonneg_t_critical`,

proved without using
`prime_term_le_at_t_critical_axiom` or
`Q_phi_shift_nonneg_t_critical`.

If neither theorem is derivable from the current repo context, return the
**strongest honest weaker theorem** or the **minimal extra assumption** that
closes exactly one of those two targets.

## Exact preferred statements

Preferred target A:

```lean
theorem Q_phi_shift_pair_nonneg_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    0 ≤ Q (phi_shift_critical B τ) + Q (phi_shift_critical B (-τ)) := by
  -- prove without sorry/exact?/admit and without using
  -- prime_term_le_at_t_critical_axiom or Q_phi_shift_nonneg_t_critical
```

Preferred target B:

```lean
theorem Q_Fejer_heat_atom_nonneg_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    0 ≤ Q (Fejer_heat_atom B t0_critical τ) := by
  -- prove without sorry/exact?/admit and without using
  -- prime_term_le_at_t_critical_axiom or Q_phi_shift_nonneg_t_critical
```

## Important facts: avoid the dead end

- Local repo notes already indicate that the old fully shifted scalar claim is
  false-for-now as a uniform theorem. There are legacy numeric notes with a large
  negative shifted value (`min Q ≈ -911` near `τ ≈ 1.69`).
- New bridge lemmas now exist in `Q3/Proofs/PrimeTerm_t_bridge.lean`:

```lean
Q3.Proofs.PrimeTermBridge.prime_term_phi_shift_tcritical_le_cap
Q3.Proofs.PrimeTermBridge.prime_term_phi_shift_tcritical_le_exp_rho_oneK
```

- But the naive scalar route through `rho_oneK` is **not** enough:
  `rho_oneK K = exp(8 * pi^2 * t_rkhs_cap * K^2) * rho_one`,
  and `exp_tcrit_to_rkhs(1) ≈ 1.2e7`, so do not try to close the theorem by
  combining `rho_one <= c_star/4` with the `t_critical -> t_rkhs_cap` bridge.

## Available context already in repo

- `Q3/Proofs/Q_nonneg_t_critical.lean`
  - `Fejer_heat_atom_eq_phi_shifts`
  - `arch_term_ge_at_t_critical`
  - current placeholders / wrappers around the blocked scalar theorem
- `Q3/Proofs/PrimeTerm_t_bridge.lean`
  - new `t_critical -> t_rkhs_cap` prime-term bridge lemmas
- `Q3/Proofs/RKHS_cap_rayleigh.lean`
  - `prime_term_phi_shift_le_rho_oneK`
- `Q3/Proofs/Q_nonneg_atoms_helpers.lean`
  - `Q_scale_add`, integrability, summability infrastructure
- `Q3/Proofs/CompatibilityReduction.lean`
  - this is the downstream consumer; keep its API stable if possible

## Preferred strategy

1. Use the decomposition
   `Fejer_heat_atom_eq_phi_shifts`
   and try to prove positivity directly on the symmetric pair or on the evenized
   atom, rather than on each shifted summand separately.
2. Reuse the new prime-term bridge lemmas only where they are honestly useful.
3. If a direct theorem is still impossible, return:
   - a provable weaker theorem with explicit statement, and
   - a tiny wrapper plan showing exactly how `CompatibilityReduction` should be
     rewired to use it.

## Constraints

- No `sorry`, no `exact?`, no `admit`.
- Do not import `Q3/Archive` or `Q3/Clean`.
- Keep the new A3_FLOOR and the old RKHS route separated; do not mix proof
  strategies implicitly.
- Prefer small explicit Lean proof steps (`simpa`, `linarith`, `nlinarith`,
  `calc`, `rw`, `have`, `refine`).
- If you cannot prove target A or B, say so explicitly and return the first
  blocked inequality/lemma rather than inventing a fake closure.

## Deliverable

Return a Lean patch that compiles in the active project and does one of:

1. proves target A,
2. proves target B,
3. or introduces the minimal honest replacement theorem/assumption for exactly
   one of them, together with the downstream wiring note.
