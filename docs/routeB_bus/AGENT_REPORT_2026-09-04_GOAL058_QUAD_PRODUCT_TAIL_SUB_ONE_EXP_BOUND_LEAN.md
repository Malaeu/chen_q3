# AGENT REPORT — GOAL058 — `FORMALIZE_QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND`

```yaml
RESULT_CODE: P59_QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND_LEAN
STATUS: DONE
DATE: 2026-09-04
BRANCH: rh_clean
DIRECTIVE_SOURCE: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_GROUND_TRANSFORM_ZERO_PINNING_AND_REAL_ZERO_IDENTIFICATION_2026-09-04.md § CODEX DIRECTIVE
REQUEST_ID: REQ-2026-09-04-ZEROPIN
COMMITTED: false
PUSHED: false
```

## 1. Exact theorem type

Declared in namespace `Q3.RouteB`, appended at the end of the target module
(before `end Q3.RouteB`), at line 1544 of the post-edit file:

```lean
theorem norm_quadProduct_sub_one_le_exp_sub_one
    (c : Multiset ℝ) (hc : ∀ a ∈ c, 0 ≤ a) (z : ℂ) :
    ‖(c.map (fun a : ℝ => 1 - (a : ℂ) * z ^ 2)).prod - 1‖
      ≤ Real.exp (‖z‖ ^ 2 * c.sum) - 1
```

Statement is verbatim the judge's target — no algebraic reformulation was
needed, so inequality direction and the zero-at-empty-tail behaviour are the
directive's own.

## 2. Files touched

- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean`
  — **append only**, `git diff --stat` = `1 file changed, 98 insertions(+)`, zero
  deletions. No existing declaration was modified. Declaration count went
  33 → 34 (`#print axioms` lines emitted by `lake env lean`: 34).
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND_LEAN.md`
  — this report.

Nothing else. No commit, no push.

## 3. Proof route actually used (boundary compliance)

Multiset induction (`Multiset.induction_on`) with the telescoping split

```
(1 - a z²) · P - 1 = (P - 1) - (a z²) · P
```

then `norm_sub_le`, `norm_sub_norm_le` to get `‖P‖ ≤ ‖P-1‖ + 1 ≤ exp S`, then
the same finite `Real.add_one_le_exp` step already used by the file's existing
private lemma `norm_quadProduct_le_exp` (line 1054), giving
`(1 + a‖z‖²)·exp S − 1 ≤ exp(a‖z‖²)·exp S − 1 = exp(a‖z‖² + S) − 1`.

Boundary check against the directive:

| Boundary | Status |
|---|---|
| one local Lean theorem | met (1 theorem + 4 `example` plants) |
| no route promotion | met |
| no Xi theorem | met |
| no zero-convergence assumption | met |
| no Hadamard/Weierstrass API | met — no infinite product, no entire-function factorization, no order predicate |
| no new sorry / admit / axiom / opaque constant | met — grep for `sorry`, `admit`, `^axiom `, `exact?` in the file returns nothing |

## 4. Commands and exit codes

All exit codes taken via `${PIPESTATUS[0]}`.

```
$ cd q3.lean.aristotle
$ lake env lean Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
  -> EXIT 0    (only `#print axioms` info lines, no errors, no warnings)

$ lake build Q3.Proofs.RouteB.Proposition59ExplicitProductCurvatureBridge
  -> EXIT 0    "Build completed successfully (7774 jobs)."

$ cd <repo root>
$ scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
  -> EXIT 0    "scan Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean"
               "q3_check ok"
```

A baseline `lake build` of the same module before the edit also returned exit 0,
so the 33 pre-existing declarations compile unchanged before and after.

## 5. Axiom profile

Emitted by the in-file `#print axioms` (line 1544 of the build log):

```
'Q3.RouteB.norm_quadProduct_sub_one_le_exp_sub_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Exactly the required triple. All 33 pre-existing declarations still report the
same triple; no `sorryAx`, no project axiom anywhere in the module.

## 6. Plants — all four compile

Provided as `example`s directly under the theorem; they are checked by the same
`lake env lean` / `lake build` run above (exit 0), so "compiles" is machine-verified,
not asserted.

- **Plant A — empty multiset gives `0 ≤ 0`.**
  `example (z : ℂ) : ‖(((0 : Multiset ℝ).map …).prod - 1)‖ = 0 ∧ Real.exp (‖z‖^2 * (0 : Multiset ℝ).sum) - 1 = 0`.
  Both sides vanish, so the bound carries no spurious constant on the empty tail.
  **COMPILES.**

- **Plant B — singleton exposes the scale `a·‖z‖²`.**
  `example (a : ℝ) (ha : 0 ≤ a) (z : ℂ) : a * ‖z‖ ^ 2 ≤ Real.exp (‖z‖ ^ 2 * a) - 1`,
  proved by instantiating the theorem at `{a}`. The left-hand side of the
  theorem specializes to `‖a z²‖ = a‖z‖²`. **COMPILES.**

- **Plant C — a negative coefficient is rejected.**
  Stated as a *negation*, so it is a machine-checked proof that the hypothesis
  `hc` is load-bearing and not decorative:
  `example : ¬ (‖(({-1} : Multiset ℝ).map (fun a : ℝ => 1 - (a : ℂ) * (1 : ℂ) ^ 2)).prod - 1‖ ≤ Real.exp (‖(1 : ℂ)‖ ^ 2 * ({-1} : Multiset ℝ).sum) - 1)`.
  At `c = {-1}`, `z = 1` the left side is `1` while the right side is
  `exp(-1) - 1 < 0`. Hence the theorem cannot be restated without `hc` unless
  `c.sum` is replaced by a sum of absolute values. **COMPILES.**

- **Plant D — `z = 0` gives `0 ≤ 0`.**
  `example (c : Multiset ℝ) : ‖((c.map (fun a : ℝ => 1 - (a : ℂ) * (0 : ℂ) ^ 2)).prod - 1)‖ = 0 ∧ Real.exp (‖(0 : ℂ)‖ ^ 2 * c.sum) - 1 = 0`.
  Degenerate for every tail, not just the empty one. **COMPILES.**

## 7. Next missing cofinal theorem (NOT proved, NOT claimed)

The judge's current smallest named gap is

```
P59_COMPLETE_ZERO_DIVISOR_TIGHTNESS_AND_TARGET_CROSSWALK
```

with the next cheapest decisive test named as
`P59_ZETA_ZERO_EVALUATION_RANGE_IDENTITY: evaluationVector = K * boundedPreimage`.
Neither is proved, attempted, or implied by this task — the tail-minus-one bound
delivered here is a normality/tightness ingredient only and does **not** supply
local zero-count convergence with multiplicity, excess-zero tightness on compacts,
escaping reciprocal-square mass control, or the complete target-divisor crosswalk.

## 8. Verdict

```
P59_QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND_LEAN
```
