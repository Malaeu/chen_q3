# Task — Goal 058: reciprocal-mode odd-Gram source preflight (READ-ONLY paper + source)

Date: 2026-09-03 (night)
Status: `AUTHORIZED_BY_JUDGE_CODEX_DIRECTIVE` (verdict `3dc82357`, `TRY_RECIPROCAL_MODE_ODD_GRAM_CURVATURE_IDENTITY`)
Executor: Codex when its API is back; meanwhile a Linux-Claude subagent (Opus) runs it — same boundaries
Mode: PAPER_AND_SOURCE_READ_ONLY — no Lean edit, no numerics, report only

```yaml
TASK_ID: GOAL058_RECIPROCAL_MODE_ODD_GRAM_SOURCE_PREFLIGHT
TARGET: P59_RECIPROCAL_MODE_ODD_GRAM_CURVATURE_IDENTITY
SUCCESS: P59_RECIPROCAL_MODE_ODD_GRAM_SOURCE_IDENTITY
FAILURE: C5_RECIPROCAL_COMMUTATOR_ONLY_RENAMES_CURVATURE
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## Read
`q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean` (`ccmWeilTau_structured_offdiag`,
`ccmWeilMatFinite_structured_offdiag`, `ccmBetaFinite_unique`, `ccmWeilMatFinite_commutator`:
`X K − K X = β ηᵀ − η βᵀ`), `CCMFiniteWeilParity.lean`, `CCMFiniteWeilSourceMatrixN1.lean`
(`ccmQKernel`, `ccmPrimeEntryN1`), `Proposition59EntireTransform.lean`; the verdict
`docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_NEW_MECHANISM_FOR_CURVATURE_WALL_2026-09-03.md` §6 in full.

## Return (judge's list)
1. exact typed definitions of X, R, η, β, b, r on the noncentral carrier (±N indexing);
2. proof or refutation of `D R − R D = b rᵀ − r bᵀ` from the source commutator (note: the source
   commutator is for the full K; restrict to the noncentral block and check what the central
   row/column contributes);
3. parity proof that `rᵀ A b = 0` (A = (D−λ₁)⁻¹ preserves reversal parity; b even, r odd);
4. exact derivation of `κ = (L²/(4π²))·E`, `E = ½‖r‖² − ⟨r,A(Rb)⟩ + (a₀−λ₁)⟨r,Ar⟩ + Σ_{n>N}1/n²`,
   including the identity `1/12 = (1/2π²)[½‖r‖² + Σ_{n>N} 1/n²]` on the symmetric carrier;
5. full source expansion of the vector `R b` (entries `b_n/n`) in CCM terms: W02 pole part,
   Arch (W_R) part, prime part — as explicit formulas, no norms;
6. the decisive question: does the odd defect `½(D−λ₁)r − Rb + (a₀−λ₁)r` admit an exact
   `(D−λ₁)`-coboundary `(D−λ₁)s` with an explicit odd s built from source rows without
   inversion, a one-sided odd source form, or a finite-rank term with an explicit L⁻² budget?
   Return SUCCESS or FAILURE code accordingly. If every estimate must start with
   ‖(D−λ₁)⁻¹‖, an absolute odd floor, or an uncontrolled mixed resolvent pairing → FAILURE.

## Forbidden
Lean edits; numerical runs; full resolvent norms; absolute floors; pole/Arch–Prime splitting of b
(Probe 7 showed each part pays 1/λ₂); post-hoc schedule changes; RH claim.

## Report
`docs/routeB_bus/AGENT_REPORT_2026-09-03_GOAL058_RECIPROCAL_MODE_ODD_GRAM_PREFLIGHT.md`
