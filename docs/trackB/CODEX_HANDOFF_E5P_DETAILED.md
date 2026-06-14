# Codex handoff — E5p same-unit bridge + penalty certificate (detailed)

**Entry point first:** read
[`TRACKB_E5P_SAME_UNIT_BRIDGE_HANDOFF.md`](TRACKB_E5P_SAME_UNIT_BRIDGE_HANDOFF.md)
— short task note (canon + sync rule + 5 deliverables).
**Then this file** — operational handbook (atlas mapping, priorities, compute
discipline, theorem refs).
**Then** [`TRACKB_E5P_THEOREM.md`](TRACKB_E5P_THEOREM.md) — paper-spec of the
target theorem, four assumptions, current status per assumption.

Read this whole stack every rebase.

**Status as of this handoff:** previous run (`d4554343f`) named the gap correctly
(`SAME_UNIT_ANALYTIC_MU_BRIDGE`) and produced a finite interval cert for
supplied μ. **That is not a closure.** This handoff supersedes
`CODEX_HANDOFF_LP_SELBERG_MOLLIFIER.md` — keep that file for history but obey
this one on conflict.

---

## 1. Naming canon — use `E5p`, never the ASCII-apostrophe spelling

The ASCII apostrophe spelling is **not** the mathematical prime symbol `′`.
To kill alias-hell we fix one ASCII canon repo-wide:

| Context           | Write                                                |
|-------------------|------------------------------------------------------|
| filenames, paths  | `E5P` or `E5p`                                        |
| code / Lean ids   | `E5p`                                                 |
| docs (prose)      | `E5p` (introduce once as `E5p = E5-prime = E5′`)       |
| commit messages   | `E5p`                                                 |
| diagrams / math   | `E5′` (the unicode prime, **U+2032**) is OK in display |
| **forbidden**     | ASCII-apostrophe spelling, `E5_prime` in new files    |

**Spoken canon** (so we and Ылша stay aligned):

- RU: «E пять штрих»
- EN: «E five prime»
- DE: «E fünf Strich»

When Ылша dictates "штрих" / "prime" — it always means `E5p`.

If you find the ASCII-apostrophe spelling in any tracked Track B file, **fix
it in the same commit you touch that file for any reason**. Do not open a
separate "naming" commit unless asked.

---

## 2. Forbidden semantics

The following identifications are **wrong** and must not be re-introduced:

```
old usable-mu-budget label  =  finite LP gap minus errors  ← WRONG
old LP-mu-budget label      =  finite LP gap               ← WRONG
B2B_LP_GREEN                ⇐  old usable label > 0        ← WRONG
```

If any tracked file still asserts these, **patch on read**.

Reasons:

- the `duality_gap` `d_K - p_K` inside the **finite** LP knows nothing
  about the analytic budget.
- Calling it "mu-budget" creates a false bridge between LP slack and the
  Weil-side analytic μ.
- `B2B_LP_GREEN` flipped by a positive duality gap is a fake closure.

---

## 3. Required semantics

Use these definitions verbatim (single source of truth: `MU_BUDGET_INTERFACE.md`):

```
certificate_gap_K  =  d_K  -  p_K  -  finite_guards_K
budget_slack_K     =  mu_K -  d_K  -  transfer_guards_K
```

Where:

- `p_K` = worst primal edge-defect Rayleigh value on the current finite K-cell
  cone.
- `d_K` = dual clamp level — the LP/SOS cost to dominate the finite edge defect.
- `mu_K` = analytic E5p edge budget (Weil-side integral).
- `finite_guards_K` = sum of all numerical guards interior to the LP (closure,
  boundary, quadrature, finite projection errors).
- `transfer_guards_K` = guards needed to transfer the finite LP clamp to the
  analytic ledger (normalization, tail, boundary).

**E5p GREEN is forbidden** unless:

1. `budget_slack_K ≥ 0` is proven (not just numerically observed), **and**
2. the same-unit `mu_K` bridge is proven (Section 4), **and**
3. the penalty PSD certificate exists (Section 5).

Two of three is not enough. Document the missing one as GAP, do not paper over.

---

## 4. The theorem we are closing

The target is `Theorem E5p_edge_closure_K` — written in
[`TRACKB_E5P_THEOREM.md`](TRACKB_E5P_THEOREM.md). Quick reference:

```
Fix K. Track B finite packet data:
  G_K       = Gram / normalization matrix
  Q_K       = boundary constraint matrix
  E_edge,K  = P_edge,K - P0_edge,K
  mu_K      = analytic E5p edge budget

Assume:
  (A1) G_K is positive definite on ker(Q_K).
  (A2) E_edge,K is exactly the finite matrix representing the raw edge
       defect in the same normalization as the E5p ledger.
  (A3) mu_K is proved in the same G-normalized units.
  (A4) ∃ tau_K ≥ 0 such that
         mu_K · G_K  -  E_edge,K  +  tau_K · Q_K^T Q_K  ≥  0.

Then:  ∀ v with Q_K v = 0,   v^T E_edge,K v  ≤  mu_K · v^T G_K v.
```

(A4) is the **machine-checkable** core. The penalty form coincides with the
quadratic form on `BoundaryNull = ker Q_K`, and a positive penalty PSD gives
the inequality on that subspace via the existing Lean receiver pattern.

---

## 5. Certificate contract (the only path to `B2B_E5P_GREEN_CERTIFIED`)

```yaml
input:
  K
  G_K
  Q_K
  P_edge_K
  P0_edge_K
  E_edge_K        # = P_edge_K - P0_edge_K
  mu_K
  tau_K
  finite_error_guards
  transfer_error_guards

checks (ALL must pass):
  1. raw-log / xi normalization matches:
       a   = r · log(p)
       xi  = a / (2π)
  2. E_edge_K is bit-for-bit the same object used by the E5p ledger
  3. mu_K is in the same G-normalized units as d_K and E_edge_K
  4. matrix
       mu_K · G_K  -  E_edge_K  +  tau_K · Q_K^T Q_K
     is PSD by a rational LDL or interval-Arb certificate
  5. tail / boundary / transfer guards are all paid in same-unit

output:
  B2B_E5P_GREEN_CERTIFIED
```

Any of checks 1–5 missing → output is **GAP** with the exact missing line, not
GREEN.

The repo's existing formal layer already distinguishes
`xi_n = log n/(2π)`, `w_Q(n) = 2Λ(n)/√n`, and
`Q(Φ) = arch_term(Φ) - prime_term(Φ)`. Freeze this normalization **before**
any E5p theorem claim — it is the bridge for check 3.

---

## 6. Rebase protocol

Codex must keep `rh_clean` clean and read this handoff every cycle.

**Before starting work in a session:**

```bash
git fetch origin
git rebase origin/rh_clean
```

**Files to re-read in this exact order:**

1. `docs/trackB/CODEX_HANDOFF_E5P_SAME_UNIT_BRIDGE.md`  (this file)
2. `docs/trackB/TRACKB_E5P_THEOREM.md`                  (theorem statement + assumptions)
3. `docs/trackB/MU_BUDGET_INTERFACE.md`                 (canonical formula source)
4. `docs/trackB/TRACKB_PRICE_TABLE.md`                  (live status of every route)
5. `docs/trackB/S5C_LP_FINITE_DUAL_FEASIBILITY.md`      (LP gate state)
6. `docs/trackB/TRACKB_REUSE_OLD_LOWER_BOUND.md`        (m_old discipline)

**Before push:**

```bash
git fetch origin
git rebase origin/rh_clean
git diff --check          # whitespace clean
```

**Hard rules (unchanged from previous handoff):**

1. NO Claude/Codex co-authoring in commits, NO AI-tags in git history.
2. Numerical claims need numerical evidence — script ref or table.
3. If a route is dead, **say so**, do not paper over.
4. Verdict `OPEN` / `GAP` is a valid result. Do not fake-close.
5. Per-K interval certificates for `K ∈ {2, 3, 3.5, …}` are **DIAGNOSTIC, not
   proof input** to E5p closure. Lean cannot kernel-reduce these grids.
   Acceptable use: finite witness for base case K₀ in a structural induction,
   nothing more.

---

## 7. What to do this run

In priority order:

### D1. Naming sweep
Replace every ASCII-apostrophe spelling in tracked Track B docs and scripts
with `E5p`.
One commit, no behaviour change. Skip Unicode `E5′` in display contexts.

### D2. Verify the bookkeeping
For each of `MU_BUDGET_INTERFACE.md`, `TRACKB_PRICE_TABLE.md`,
`S5C_LP_FINITE_DUAL_FEASIBILITY.md`, `TRACKB_LP_REFORMULATION.md`:

- assert exactly the formulas from Section 3 (with `finite_guards_K` /
  `transfer_guards_K` explicit),
- patch any remaining old LP-mu-budget or old usable-mu-budget labels to the
  new semantics,
- do NOT touch Lean files.

### D3. Same-unit bridge attempt — try IN THIS ORDER

**B (mollifier, atlas card 028).** Smallest scope. Check whether the Track B
margin admits an inverse Dirichlet expansion in K-cell coefficients. If YES →
draft `TRACKB_E5P_MOLLIFIER_BRIDGE.md` with the second-moment computation and
the conditional density-1 deliverable shift. If NO → write a 5-line dead-end
note and move on.

**A (Selberg extremals, atlas card 009).** Replace `C · exp(-D)` edge bounds
with Beurling-Selberg sharp constants of bandwidth K. Goal: a closed-form
analytic lower bound for `mu_K` in G-normalized units (this is **assumption
(A3)** of the theorem). Sign direction must be checked explicitly, not
assumed.

**C (Connes adelic class space, atlas card 029, hot_candidate).** Heavier path:
re-frame the bridge in the adelic class space where archimedean and finite
places carry the same normalization by construction. This is the architectural
fix for (A3). High effort, high reward.

If B and A both produce dead-end notes within their budget, **stop and
escalate** — do not fall into per-K interval grinding.

### D4. Lean nothing yet
Do not touch Lean proof files in this run. The theorem statement in
`TRACKB_E5P_THEOREM.md` is a paper specification first; we Lean-formalize
**after** the math route is closed on paper.

### D5. Update price table
Reflect the outcome of D3 with one of:

- `S5C_E5P (mollifier)` → `<verdict from D3-B>`
- `S5C_E5P (Selberg analytic mu_K)` → `<verdict from D3-A>`
- `S5C_E5P (Connes adelic)` → opened-or-not, with effort estimate

Route D (finite ledger fallback) stays demoted: touch only if D3-B, D3-A and
D3-C are all confirmed dead.

---

## 8. Atlas reminder (closed-form moves only, not grid sweeps)

Trick atlas lives at
`/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/`.

The three cards relevant to E5p:

| id   | name                       | role for E5p closure                         |
|------|----------------------------|-----------------------------------------------|
| 020  | Cohn-Elkies LP framework   | finite LP primal/dual — already applied      |
| 028  | Conrey-Ghosh mollifier     | density-1 bridge (D3-B)                       |
| 009  | Selberg extremals          | sharp analytic edge constants for mu_K (D3-A) |
| 029  | Connes adelic class space  | architectural single-unit fix (D3-C)          |

Read the card file directly before invoking the move — `q3_translation` and
`must_survive` fields are the spec.

---

## 9. Honest verdict (frame this run by it)

```
possible theorem route:  YES
currently proved:        NO
current LP dictionary:   RED until same-unit mu_K bridge proved
old Step32F reserve:     NOT USABLE AS PRE-EDGE BUDGET (would double-count)
next necessary object:   same-unit mu_K bridge + rational/interval PSD cert
                         for  mu_K · G_K - E_edge_K + tau_K · Q_K^T Q_K ≥ 0
                         + final E5p ledger theorem
```

This is the only path. No "another LP GREEN" shortcut.
