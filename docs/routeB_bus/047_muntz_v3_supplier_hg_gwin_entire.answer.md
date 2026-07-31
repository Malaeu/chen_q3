HG_SUPPLIER_DISCHARGED_FOR_V3_CLASS

```yaml
PRIMARY: HG_SUPPLIER_DISCHARGED_FOR_V3_CLASS
PRIMARY_COUNT: 1
FAILURE_CODE: null
SCOPE: ABSTRACT_SUPPLIER
VERIFIER: LEAN
ROUTE_STATE: CHALLENGER_NOT_RH
STATE_PROMOTION: false
BUS_010: VOID
ARISTOTLE_SUBMISSIONS_THIS_CYCLE: 0
FROZEN_FILES_CHANGED: 0
R6EXPORT_FILES_CHANGED: 0
MUNTZ_R6_FILES_CHANGED: 0

GOAL_VERSION_CONSUMED:
  FILE: 047_muntz_v3_supplier_hg_gwin_entire.goal.md
  SHA256: da6e15e37307b65af85abdcd4eb45834c0a0284aea917fc9199cd5e12fde56b9

PRIMARY_THEOREM:
  NAME: gwin_entire
  FILE: RequestProject/MuntzV3GwinExactClass.lean
  FILE_SHA256: a433b05d9e798b98a45839b7510dab7199655110cc4de9a764568e2c3e13490c
  LOC: 190
  AXIOMS: [propext, Classical.choice, Quot.sound]
  TAINT_MATCHES: 0

CONSUMER_COROLLARY:
  NAME: gwin_analyticOnNhd_shiftedHalfPlane_v3Class
  AXIOMS: [propext, Classical.choice, Quot.sound]

PL1_PLANT:
  NAME: pl1Witness_gwin_entire
  RESULT: ACCEPT
  FILE: RequestProject/MuntzV3GwinExactClassPL1Plant.lean
  FILE_SHA256: 72183fd2c44fd9004351517a79560a8ce0127712d339f514ce64ee3ebe8ba474
  LOC: 42
  AXIOMS: [propext, Classical.choice, Quot.sound]

DEPENDENCY_PLANT:
  RESULT: ACCEPT
  HMASS: absent
  POSITIVE_LOWER_SUPPORT: absent
  GLOBAL_LIPSCHITZ_WITH: absent
  R6_IMPORT_OR_SUPPLIER_CALL: absent
```

All theorem and plant claims are `[ABSTRACT][LEAN]`; hashes are
`[CONTROL][SHA256]`, while route, bus, frozen, dependency, and submission
fields are `[CONTROL][LOCAL]`.

## Exact declarations delivered

```lean
theorem gwin_entire
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Differentiable ℂ (Gwin h Λ)

theorem gwin_analyticOnNhd_shiftedHalfPlane_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    AnalyticOnNhd ℂ (Gwin h Λ) shiftedHalfPlane
```

The primary theorem has exactly the requested v3 class.  There is no mass
hypothesis, positive lower support, global `LipschitzWith`, or R6 dependency.
`[ABSTRACT][LEAN]`

## Proof route

1. From `1≤Λ`, obtain `0<Λ` and fix
   `N = ceil(|b|*Λ)+1 : ℕ+`, `S=Finset.Icc 1 N`.
2. If `u∈Ioo Λ⁻¹ Λ` and `n>N`, then `1<Λ*u` and
   `|b|*Λ<n`; positivity of `Λ` gives `b<n*u`.  Hence the support
   condition kills every term outside `S`.
3. Rewrite the `Estar` tsum on the entire window as one finite sum.  Its
   product with `sqrt u` is measurable directly from `hmeas`.
4. Reuse the exact 046 estimate
   `C=‖h 0‖+(K:ℝ)|b|` on `Ico 0 b`.
5. For each `n∈S`, exclude the sole endpoint `u=b/n` almost everywhere.
   `Filter.eventually_all_finset` combines the finite singleton-null
   exclusions.
6. Bound the window indicator by
   `D=sqrt Λ * card(S) * C`; measurable plus a.e. constant-bounded gives
   `LocallyIntegrableOn` via `locallyIntegrableOn_const.mono`.
7. The indicator is identically zero near zero (below `Λ⁻¹`) and at infinity
   (above `Λ`), so all required Mellin big-O estimates are zero estimates.
8. Rewrite `Gwin h Λ` as the Mathlib Mellin transform of that indicator and
   apply `mellin_differentiableAt_of_isBigO_rpow` at every `s : ℂ`.
9. Restrict global differentiability to the open `shiftedHalfPlane` using
   `DifferentiableOn.analyticOnNhd`.

The primary file imports only
`RequestProject.MellinCompactSupportAnalyticity`.  The sealed R6 window file
was read only as a proof-shape template. `[CONTROL][DEPENDENCY_AUDIT]`

## Mandatory plants

### PLANT-1 — actual PL1 witness

**ACCEPT.**  The plant instantiates `gwin_entire` with the actual source-locked
witness

```text
pl1Witness(u) = 1_(0,1](u) * u
b = 1
K = 1
Λ = 1
```

Its endpoint jump at `1` and nonzero mass `1/2` do not enter the theorem.
Because the existing witness certificates are private to Goal 042, the
42-line plant reassembles only measurability, support, and the
`LipschitzOnWith 1` certificate.  The first substantive plant elaboration
passes with the standard axiom triple. `[ABSTRACT][LEAN]`

### PLANT-2 — forbidden-dependency audit

**ACCEPT.**  Both new files were scanned for

```text
hmass
0 < a
LipschitzWith
R6Export
Gwin_differentiable
```

with word-sensitive matching; the result is zero matches.  The only imports
are the exact v3 support/Mellin bridge, the new primary theorem, and the actual
PL1 witness module. `[CONTROL][DEPENDENCY_AUDIT]`

## Why this closes both hG columns

No separate R6 theorem is required.  Given the R6 hypotheses:

- global `LipschitzWith K h` supplies `hlip.continuous.measurable` and
  `hlip.lipschitzOnWith`;
- support in `Icc a b` with `0<a` implies zero extension outside
  `Icc 0 b`, since `Icc a b ⊆ Icc 0 b`;
- the same `1≤Λ` is passed unchanged.

Thus the exact-class theorem strictly subsumes the R6 hG column by restriction;
no R6 analytic supplier or extra mass input is involved.

## Canonical supplier ledger

```text
Goal 044 hRm: PROVED ON R6 LIBRARY CLASS ONLY
Goal 045 hRp: PROVED ON R6 LIBRARY CLASS ONLY
Goal 046 hRp: PROVED ON EXACT V3 / CANONICAL CLASS
Goal 047 hG:  PROVED ON EXACT V3 CLASS; R6 COLUMN FOLLOWS BY RESTRICTION
canonical hRp: PROVED
canonical hG:  PROVED
canonical hRm: OPEN
canonical habs: OPEN (Goal 048 inventory selected export route only)
CANONICAL SUPPLIERS: 2/4
```

Goal 047 does not bundle or claim progress on hRm or habs.

## Validation ledger

```text
[ABSTRACT][LEAN] lake env lean MuntzV3GwinExactClass.lean             PASS
[ABSTRACT][LEAN] lake build RequestProject.MuntzV3GwinExactClass     PASS (8028 jobs)
[ABSTRACT][LEAN] lake env lean MuntzV3GwinExactClassPL1Plant.lean    PASS
[ABSTRACT][LEAN] full v3 lake build                                  PASS (8044 jobs)
[ABSTRACT][LEAN] #print axioms gwin_entire                           [propext, Classical.choice, Quot.sound]
[ABSTRACT][LEAN] #print axioms consumer corollary                    [propext, Classical.choice, Quot.sound]
[ABSTRACT][LEAN] #print axioms PL1 plant                             [propext, Classical.choice, Quot.sound]
[CONTROL][TAINT] both new Lean files                                 0 matches
[CONTROL][DEPENDENCY] forbidden dependencies                         0 matches
[CONTROL][MIRROR] canon versus mirror, both Lean files               IDENTICAL
[CONTROL][GIT] R6Export and both muntz_r6 trees changed              0
[CONTROL][LOCAL] Aristotle submissions                               0
```

The only full-build warnings are pre-existing sealed R6Export lints; neither
new file emits a warning.

None of the fail-closed codes fired:

```text
HG_ESTAR_WINDOW_BOUND_GAP
HG_MEASURABILITY_GAP
PLANT_NOT_DETECTED
LEAN_BUILD_FAIL
```

## Prediction score

- `P047-1`: **MISS**.  The proof route transferred exactly, but explicit
  finite-cutoff arithmetic, endpoint firewall, local-integrability assembly,
  and permanent axiom prints make the primary file 190 lines rather than at
  most 120.
- `P047-2`: **HIT**.  The actual PL1 witness passed on its first substantive
  elaboration after the primary `.olean` was built, and the forbidden-
  dependency plant was clean on its first scan.
- `P047-3`: **HIT**.  The R6 column follows directly by restriction to the
  exact v3 class; no separate R6 lemma was materialized.

## ACTIONS LOG

```text
1.  Checked rh_clean and attempted the required pull first.                     DONE
2.  Retried with pull.rebase=false; git pull --ff-only reported up to date.      PASS
3.  Locked both Goal 047 copies at da6e15e3...de56b9.                           PASS
4.  Read Route B state/control/bus and ran routeb_status.py --check.             PASS
5.  Read Goal 046 endpoint proof and sealed R6 window template.                  DONE
6.  Ran four q3_docs queries and official Mathlib API search.                    DONE
7.  Implemented fixed-window finite-sum measurability and endpoint-null bound.   PASS
8.  Closed compact Mellin differentiability and consumer restriction.            PASS
9.  Instantiated the actual PL1 witness.                                         ACCEPT
10. Ran direct Lean, isolated target build, and full 8044-job build.             PASS
11. Audited axioms, taint, forbidden dependencies, and sealed trees.             PASS
12. Mirrored both new Lean files byte-identically.                               PASS
13. Emitted no Aristotle submission, commit, or route promotion.                 PASS
14. Added one non-promoting state-history row last.                              DONE
```

## MYTHOS_PROSHKA_HANDOFF

```text
PRIMARY: HG_SUPPLIER_DISCHARGED_FOR_V3_CLASS
GOAL_SHA256: da6e15e37307b65af85abdcd4eb45834c0a0284aea917fc9199cd5e12fde56b9
THEOREM: gwin_entire
COROLLARY: gwin_analyticOnNhd_shiftedHalfPlane_v3Class
CLASS: exact v3 / measurable + Icc(0,b) support + Ico LipschitzOnWith + 1≤Λ
PROOF_ENGINE: fixed finite dilation cutoff + endpoint-null firewall + compact Mellin
PL1_PLANT: ACCEPT
DEPENDENCY_PLANT: ACCEPT
FORBIDDEN_R6_INPUTS: absent
R6_COLUMN: follows by restriction; no separate analytic lemma
LEAN: direct PASS; isolated build PASS; full build PASS (8044 jobs)
TAINT: zero
AXIOMS: [propext, Classical.choice, Quot.sound]
FROZEN_AND_R6EXPORT: untouched
ARISTOTLE: no submission
CANONICAL_HG: PROVED
CANONICAL_HRP: PROVED
CANONICAL_HRM: OPEN
CANONICAL_HABS: OPEN
CANONICAL_SUPPLIERS: 2/4
ROUTE: CHALLENGER / NOT_RH
BUS_010: VOID
```
