# Task — Goal 058: normalized-ξ lattice eigen-equation preflight (paper + source, READ-ONLY)

Date: 2026-09-04
Status: `AUTHORIZED_BY_JUDGE` — `CHEAPEST_NEXT_ACTION` of verdict `f788d2fa` (`REQ-2026-09-03-LATTICEWALL`); mode `PAPER_AND_SOURCE_READ_ONLY`
Executor: Codex (Fable launcher for paper reasoning) or a Linux-Claude Opus agent if Codex is down; prefix `[Linux-Codex][rh_clean][Goal058]` or `[Linux-Claude-Agent][rh_clean][Goal058]`
Author: Linux-Claude (observer), transcribing the judge

```yaml
TASK_ID: GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
JUDGE_PREDICTION: [P_LOW_MODE_RECURRENCE_CLOSES_BEFORE_GAP, 0.40]
SUCCESS_CODE: P59_XI_LATTICE_LOW_MODE_STABILITY_IDENTITY
FAILURE_CODE: P59_XI_LATTICE_EQUATION_REIMPORTS_DENSE_TAIL_OR_GAP
CLOSES_IF_SUCCESS: [P59_WEIGHTED_LATTICE_ERROR_SOURCE_BOUND (route to)]
OPENS: []
```

## Object (judge Q4, exact)

Even CCM block `K̃` on the production schedule `m = N = k+2`, `L = log m`, in the
even-basis coordinates of `docs/routeB_bus/phase5_scripts/edge_ledger_build.py::parity_blocks`
(√2 scaling of `n = 0` exactly as there). Ground row `ξ`, center-normalized `y = ξ/ξ_0`
(`y_0 = 1`). The eigen-equation `K̃ξ = λ_1 ξ` written WITHOUT λ_1 and WITHOUT any inverse:

    R(y)_n := (K̃ y)_n − y_n · (K̃ y)_0 = 0   for all n = 1..N.

Target statement (`P59_XI_LATTICE_LOW_MODE_STABILITY_IDENTITY`): at low modes `n ≤ n_0(L)`
the equation `R(y)_n = 0` is a recurrence (or a one-sided bound) for `y_n` in terms of
`y_0..y_{n−1}` and the SOURCE entries of `K̃` alone, whose coefficients are bounded by
source formulas (`ccmWeilTau_structured_offdiag`, `W02` pole split, prime sum ≤ m), and
whose remainder (the coupling to modes `> n_0`) is bounded WITHOUT `‖(D−λ_1)⁻¹‖`, without
an absolute gap, without an odd-sector floor, and without a dense-tail sum that reimports
the collapsed complement.

## Steps

1. Read the source: `CCMFiniteWeilSourceCommutator.lean`, `CCMFiniteWeilSourceMatrixN1.lean`,
   `Proposition59EntireTransform.lean`, `edge_ledger_build.py::parity_blocks`, the verdict
   `f788d2fa` (Q3–Q4), the wall card `docs/routeB_bus/WALL_OBJECT_CARD_2026-09-03.md`.
2. Write `R(y)_n = 0` explicitly for `n = 1, 2, 3` in source entries (Arch, Prime, pole
   parts). Name every coefficient by its source formula.
3. Decide BEFORE any norm: does the equation at mode `n` close on modes `≤ n` up to a
   remainder that is a SUM over `n' > n_0` with an explicit source coefficient decay?
   If the remainder needs the full row `y_{n'}` for all `n' ≤ N` with no decay of the
   coefficient, that is the dense tail; issue the failure code.
4. Two-by-two plant `K_t = [[λ + b²/t, b],[b, λ + t]]`: any argument that would bound `y_1`
   for the plant is generic and must be rejected (the plant has `y_1 = −b/t`, arbitrary).
5. Return exactly one code and, on success, the exact typed recurrence and the remainder
   bound with its hypotheses, Lean-ready or marked NEW_ANALYTIC.

## Forbidden

`‖(D−λ_1)⁻¹‖`, uniform absolute gap, odd-sector floor, assuming the desired bound,
any numerical run (this is a paper task; the numerical companion is a separate precommit),
any edit under `phase5_scripts/`, precommit, queue, verdict; no Lean edit; no route
promotion; no RH claim.

## Report

`docs/routeB_bus/CODEX_REPORT_2026-09-04_GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT.md`
(or `AGENT_REPORT_…`): explicit equations for `n = 1..3`, the closure decision, the first
surviving remainder term with its source formula, plant check, code, and in one paragraph
what the numerical companion should measure (which remainder, which cells).
