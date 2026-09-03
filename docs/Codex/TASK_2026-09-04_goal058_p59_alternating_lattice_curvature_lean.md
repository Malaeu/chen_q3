# Codex task — Goal 058: alternating lattice curvature (Lean), six judge-listed items

Date: 2026-09-04
Status: `PREPARED_AWAITING_TRANSACTION` — judge `f788d2fa` §CODEX DIRECTIVE: "No execution is
authorized. A later transaction may formalize the six Lean-ready items." Do not start until
Linux-Claude or the owner opens the transaction.
Parent: verdict `f788d2fa` (`REQ-2026-09-03-LATTICEWALL`); builds on
`Proposition59ExplicitProductCurvatureBridge.lean` (KERNEL_GREEN 2026-09-03)

```yaml
TASK_ID: GOAL058_P59_ALTERNATING_LATTICE_CURVATURE_LEAN
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
TARGET_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean
EXPECTED_AXIOMS: [propext, Classical.choice, Quot.sound]
```

## Items (judge order; each kernel-green before the next)

1. `alternating eta-two sum` — `Σ_{n≥1} (1 + 2(−1)^n)/n² = 0` (from `hasSum_zeta_two` and the
   alternating zeta value `η(2) = π²/12`; name the Mathlib fact used).
2. `normalized P59 sample` — `F(x_n)/F(0) = (−1)^n v_n / v_0` from
   `proposition59PoleKernel_at_lattice_sign` and `proposition59RawTransform_at_zero_eq_sqrt`.
3. `alternating curvature identity` —
   `κ_F = 2 Σ_{n=1}^{N} (−1)^n (F(x_n)/F(0) − 1)/x_n² − (L²/(2π²)) Σ_{n>N} (−1)^n/n²`,
   from `proposition59_curvature_closed_form` and items 1–2.
4. `alternating tail bound` — `|Σ_{n>N} (−1)^n/n²| ≤ 1/(N+1)²` (alternating series remainder),
   hence `|T| ≤ L²/(2π²(N+1)²)`.
5. `weighted curvature inequality` — for any `f : ℝ → ℝ`, with `Δ_n := F(x_n)/F(0) − f(x_n)`,
   `W := Σ_{n≤N} |Δ_n|/n²`, `S_f := 2Σ_{n≤N}(−1)^n (f(x_n) − 1)/x_n²`:
   `κ_F ≤ S_f + (L²/(2π²)) W + |T|`.
6. `projective weighted-node inequality` — with a second even row `q` (trial), `A` the
   phase-aligned overlap, `p` the projective defect:
   `Σ_{n≤N} |F_v(x_n)/F_v(0) − F_q(x_n)/F_q(0)|/n² ≤ π²/(√45·|v_0-normalization|)·|A|·√(L·p)`
   — transcribe the exact constant and normalization from the verdict Q3 before typing; if the
   verdict's normalization is ambiguous, STOP with `P59_PROJECTIVE_NODE_INEQUALITY_NORMALIZATION_GAP`.

## Validation

```
q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean
                   lake build Q3.Proofs.RouteB.Proposition59AlternatingLatticeCurvature
repo root:         scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59AlternatingLatticeCurvature.lean
```
No `sorry`, no new axiom, no cofinal claim from finite identities. Report:
`docs/routeB_bus/CODEX_REPORT_2026-09-04_GOAL058_P59_ALTERNATING_LATTICE_CURVATURE_LEAN.md`.
