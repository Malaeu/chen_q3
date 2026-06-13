# TASK: Track B — apply 3 atlas tricks (020 + 028 + 009)

## Context

Track B price-table — single control panel:
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/docs/trackB/TRACKB_PRICE_TABLE.md`

State as of commit `600c818f4`:

- S3 closure green (bookkeeping)
- S4 product lift `Mplus*F_v` dead
- S5.1 signed-small repair dead (negative mass ~0.5)
- Route B: clipping fixes PSD, breaks edge-control
- S5C0 Route C: surcharge confirmed, `tax/mu` OPEN
- Route D: finite-ledger fallback (last resort, NOT this task)

Missing key quantity: `mu_budget(K)`.
Goal: avoid Route D by applying 3 atlas-cards as alternative routes.

## Trick atlas (READ FIRST, in this order)

Base path:
`/Users/emalam/Documents/GitHub/prowka-bot/Projects/math-arsenal/atlas/`

1. `020-cohn-elkies-lp.md` — **PRIMARY** (hot_candidate)
2. `028-conrey-ghosh-mollifier.md` — **SECONDARY** (HIT prediction)
3. `009-selberg-extremals.md` — **TERTIARY** (edge-control repair)

Cross-refs (read if needed):

- `007-dual-certificate.md` (SOS framework, related to 020)
- `008-mss-interlacing.md` (alternative averaging move)

Each card has 7 fields: `mechanism` / `applicability_signature` /
`q3_translation` / `must_survive` / `dropped_structure` /
`unconditional_input` / `status`. The `q3_translation` field in 020 already
contains the LP-dual formulation in Track B vocabulary — start from there,
do not re-derive.

---

## Deliverable 1: `TRACKB_LP_REFORMULATION.md` (~3 pages)

Path:
`/Users/emalam/Documents/GitHub/rh_lean_01_2026/docs/trackB/TRACKB_LP_REFORMULATION.md`

### Structure

#### Primal
- Weil quadratic form over admissible test functions in `eps`-budget
- Explicit cone definition (which test functions are admissible)

#### Dual
- Magic-function witness with prescribed sign on F2 margin
- Stay inside `eps`-budget
- Clamp ratio: `f(0)/f_hat(0)`

#### `mu_budget(K)` as LP-gap
- Formula: `mu_budget(K) = ...` (LP-gap of primal/dual)
- This REPLACES the "open" entry in price-table

#### Feasibility check protocol
- Numerical procedure to check whether dual is feasible at given K
- Must reuse existing K-cell infrastructure (do not invent new objects)

#### Failure-mode diagnostic (from card 020 `must_survive`)
- Check: does F2 margin break Fourier-self-dual structure?
- If yes → EXPLAINS why tax confirmed but mu open (S5C0 Route C diagnosis)

### Acceptance gates

- [ ] LP primal/dual written in Track B vocabulary (not generic)
- [ ] `mu_budget(K)` defined as concrete LP-gap, not "to be defined"
- [ ] Feasibility check protocol references EXISTING scripts in
      `rh_lean_01_2026/q3.lean.aristotle/scripts/` where applicable
- [ ] Failure-mode diagnostic gives a numerical test, not philosophy

---

## Deliverable 2: `TRACKB_SELBERG_ROUTE_B_REPAIR.md` (~2 pages)

Path:
`/Users/emalam/Documents/GitHub/rh_lean_01_2026/docs/trackB/TRACKB_SELBERG_ROUTE_B_REPAIR.md`

Replace Route B hard-clipping with Beurling-Selberg band-limited extremal of
band-width K. Goal: preserve PSD (band-limited ⇒ PSD survives) WHILE keeping
EXACT edge-effect constants instead of clip-and-bound losses.

### Structure

#### Current Route B status
- clipping fixes PSD, breaks edge-control (quote price-table)

#### Selberg majorant/minorant choice
- Which direction (majorant or minorant) does the explicit-formula sign demand?
- Verify Selberg extremal of width K respects this sign

#### Sharp edge constant
- Replace `C*exp(-D)` bound with Selberg-exact constant
- Numerical comparison: how much edge-control margin recovered?

#### Symmetry caveat (from card 009 `dropped_structure`)
- Selberg extremals not always symmetric
- Check explicit-formula sign structure not broken

### Acceptance gates

- [ ] Sign direction explicitly checked, not assumed
- [ ] Edge-effect constant given numerically, not as "improvement"
- [ ] Verdict: does this UNDIE Route B in the price-table? Yes/No w/ evidence

---

## Deliverable 3: `TRACKB_MOLLIFIER_S51_REVIVAL.md` (~2 pages)

Path:
`/Users/emalam/Documents/GitHub/rh_lean_01_2026/docs/trackB/TRACKB_MOLLIFIER_S51_REVIVAL.md`

S5.1 signed-small repair died (negative mass ~0.5). Revive via K-mollifier:
pre-multiply margin functional on K-cell by tunable finite `M_K` (combination
of edge-defect indicators), trade uniform per-cell bound for
positive-proportion of K where E5'-budget stays open.

### Structure

#### Why S5.1 died
- negative mass ~0.5 → Cauchy-Schwarz ratio collapses

#### K-mollifier `M_K` construction
- finite tunable combination of edge-defect indicators
- coefficients optimized against inverse Dirichlet expansion of margin
- This step is the REAL cost (see card 028 `unconditional_input`)

#### Second moment
- `E_K[(margin * |M_K|^2)] / (E_K[margin * |M_K|^2])^2` stays bounded
- ⇒ positive proportion of K where Gate holds

#### Deliverable shift
- Was: uniform `Gate(K)` for all K
- Now: `Gate(K)` for positive-proportion family with density → 1
- This MOVES Track B from "stuck" to "conditional live result"

#### Feasibility check
- Does our margin admit an inverse Dirichlet expansion in K-cell coefficients?
- If no → mollifier collapses to noise rescale, document this and stop

### Acceptance gates

- [ ] `M_K` written down as explicit finite combination, not abstract
- [ ] Feasibility of inverse Dirichlet expansion CHECKED (yes/no with evidence)
- [ ] If "no" → doc says so honestly, no fake-positive
- [ ] Clear statement: deliverable shifts from uniform to positive-proportion

---

## Deliverable 4: update `TRACKB_PRICE_TABLE.md`

After D1–D3, update the control panel:

- Add row "S5C0 Route C (LP)" → `mu_budget(K) = LP-gap`, status: COMPUTABLE
- Update Route B row → "Selberg repair: \<verdict from D2\>"
- Add row "S5.1 (mollifier)" → "\<verdict from D3\>"
- Route D demoted to "fallback only if D1/D2/D3 all fail"

---

## Hard rules

1. **NO** Claude/Codex co-authoring in commits, **NO** AI-tags in git history.
2. Each deliverable cites the specific atlas card by id + path.
3. Numerical claims need numerical evidence (script ref or table).
4. If a route is dead at the end of D1/D2/D3, **SAY SO** — do not paper over.
5. Verdict "open" is also a valid result. Do not fake-close.
6. `git diff --check` clean before commit. One commit per deliverable OK.
7. After all 4 deliverables: push, verify `origin/rh_clean...HEAD == "0 0"`,
   make bundle.

## Out of scope

- Route D finite ledger (touch only if D1/D2/D3 all confirmed dead).
- New atlas cards (use existing 020/028/009 only).
- Lean formalization (that comes after price-table decision lands).

## Done criteria

- 4 new/updated MD files committed and pushed.
- Price-table now answers "Where does `mu_budget(K)` come from?" → "LP-gap" or
  honest "still open after Selberg+mollifier attempts".
- One commit message that names all 3 atlas cards by id.
