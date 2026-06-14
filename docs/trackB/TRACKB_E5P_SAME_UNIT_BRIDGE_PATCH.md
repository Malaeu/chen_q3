# Patch summary — naming canon + same-unit bridge

This file lists the concrete edits Codex applies in **D1** (naming sweep) and
**D2** (bookkeeping verification) of the current handoff. Treat it as the
diff plan; the source of truth is
`CODEX_HANDOFF_E5P_SAME_UNIT_BRIDGE.md`.

---

## 1. ASCII canon sweep — `E5'` → `E5p`

Files known to still contain `E5'` (apostrophe) after the previous run.
**Replace ALL occurrences with `E5p`**, except in display-math contexts where
the Unicode prime `E5′` (`U+2032`) is acceptable.

Suggested command (review hits first, don't blanket-sed):

```bash
grep -rln "E5'" docs/trackB/ scripts/ | xargs -I{} \
  sh -c 'echo "-- {} --"; grep -n "E5'\''" {}'
```

Then for each file, replace `E5'` → `E5p` and commit as one logical unit.
Do not touch Lean files in this sweep.

Verification:

```bash
! grep -r "E5'" docs/trackB/ scripts/ | grep -v '′'
```

(Exit 0 means clean.)

---

## 2. Bookkeeping uniformity — three formulas, one definition

The following formulas must appear **verbatim** as definitions in
`MU_BUDGET_INTERFACE.md` (canonical) and be **cross-referenced** elsewhere
(no copies that drift):

```
certificate_gap_K  =  d_K  -  p_K  -  finite_guards_K
budget_slack_K     =  mu_K -  d_K  -  transfer_guards_K
```

The third one stays as a **diagnostic only**, with explicit caveat that it is
not a closure:

```
usable_budget_slack_K = mu_K - d_K - closure_error_K
                              - boundary_error_K
                              - quadrature_error_K
                              - finite_projection_error_K
```

### Files to scan and harmonize

| File                                     | Required edit                                                  |
|------------------------------------------|----------------------------------------------------------------|
| `MU_BUDGET_INTERFACE.md`                 | canonical definitions live here; ensure both formulas appear   |
| `TRACKB_PRICE_TABLE.md`                  | replace any `mu_budget_LP = d_K - p_K` with `certificate_gap_K` |
| `S5C_LP_FINITE_DUAL_FEASIBILITY.md`      | gate condition uses `budget_slack_K`, not `d_K - p_K`           |
| `TRACKB_LP_REFORMULATION.md`             | section "mu-budget interface" must point to `MU_BUDGET_INTERFACE.md` |
| `CHECKPOINTS.md`                         | naming history note kept; current entries use new names         |
| `VERDICT_B2B.md`                         | verdict uses `budget_slack_K ≥ 0` after same-unit bridge proof  |

After all edits:

```bash
! grep -rE 'mu_budget_(LP|usable)' docs/trackB/   # no hits
! grep -rn  'd_K - p_K'        docs/trackB/ | grep -vE 'certificate_gap|duality_gap'  # no hits
```

---

## 3. Forbidden flips — the LP-GREEN trap

Add to `S5C_LP_FINITE_DUAL_FEASIBILITY.md` near the gate logic, verbatim:

```
B2B_LP_GREEN is forbidden as a closure of E5p.
It is at most a finite-LP signal. Closure requires:

  (i)  budget_slack_K ≥ 0 (same-unit), AND
  (ii) same-unit mu_K bridge proven (TRACKB_E5P_THEOREM.md assumption A3), AND
  (iii) penalty PSD cert mu_K·G_K - E_edge_K + tau_K·Q_K^T Q_K ≥ 0 (A4).

Missing any one → status = GAP, not GREEN.
```

---

## 4. Old reserve discipline (`m_old = 0`)

Confirm `TRACKB_REUSE_OLD_LOWER_BOUND.md` still asserts:

> `m_old = 0`. The old Step32F LDL certificate is a **pattern** for the
> receiver, not a **reserve** to spend. Using it as a free pre-edge budget
> would double-count edge prime support already in `C = A - P`.

If anywhere in repo the old reserve is added to `mu_K` or to
`budget_slack_K`, **kill that addition** in this patch.

Verification:

```bash
! grep -rE 'm_old\s*>\s*0|m_old\s*\+'    docs/trackB/ scripts/
```

---

## 5. Theorem-shape anchor

`TRACKB_E5P_THEOREM.md` is the **paper specification**. Until each
sub-lemma in §4 of that file has its own evidence file under
`docs/trackB/lemmas/`, any claim of E5p closure is **GAP**, not GREEN.

Codex creates `docs/trackB/lemmas/` when work on (A1) starts. Empty dir is
allowed; preemptive stubs are not.

---

## 6. Sanity tests after D1 + D2

Run before commit:

```bash
git fetch origin
git rebase origin/rh_clean
git diff --check                                     # whitespace clean
! grep -r "E5'" docs/trackB/ scripts/ | grep -v '′'  # no ASCII apostrophe
! grep -rE 'mu_budget_(LP|usable)' docs/trackB/      # no forbidden semantics
! grep -rn 'd_K - p_K' docs/trackB/ \
       | grep -vE 'certificate_gap|duality_gap|cert/gap_K|gap inside'
```

All four `!`-checks must exit 0 (no matches).

Commit message:

```
[MacOS][rh_clean][TrackB] E5p naming canon + bookkeeping harmonization
```

No co-author lines, no AI tags.
