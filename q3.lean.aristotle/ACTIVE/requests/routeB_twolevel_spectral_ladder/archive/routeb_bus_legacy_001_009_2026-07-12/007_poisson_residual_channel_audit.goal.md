# BUS GOAL 007 — PoissonResidualChannelAudit_v1

STATUS: READY.
SCOPE: NOT_RH; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.

## Purpose

Resolve the exact ambiguity exposed by bus 006.

Bus 006 proved that extending the currently implemented Poisson sum from
`k <= 8` to `k <= 40` does not close the direct/Poisson mismatch.

The remaining explanations are:

1. the same signed Poisson channel converges only after a longer tail;
2. an explicit pole / midpoint / boundary / second-edge channel is absent;
3. the direct and Poisson computations represent different canonical objects;
4. the available tail bound is too weak to decide.

This gate must derive an exact residual ledger before adding or fitting any
new channel.

This is the cheapest decisive falsifier upstream of:

- ConnesInstrumentRecheck;
- ProjectedProlateDefectEquation;
- PoissonLeakageFactorization;
- Gate 6.

Do not attempt any of those downstream gates here.

---

## Immutable inputs

Read but do not modify:

- `bus/006_leakage_closeout.goal.md`
- `bus/006_leakage_closeout.answer.md`
- `out/leakage_closeout_v1.json`
- `leakage_closeout_v1.py`
- `true_precision_packet_gate_v1.py`
- `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md`
- `docs/PEN_3_1_4a_LEFT_EDGE_v3.md`
- `ROUTE_B_STATE.md`

Pinned facts from completed gates:

- `h0 <-> chi0`
- `h4 <-> chi2`
- `C = 2*pi*lambda^2`
- working cell: `lambda^2 = 13`, `N = 120`
- canonical packet has exact integral zero
- canonical packet has exact `h_lambda(0) != 0`
- branch: `H2-POLE/CORRECTION`
- midpoint / half-weight convention is locked
- the current `k <= 40` Poisson partial sum differs from the direct value by
  `0.0651060246` relatively
- the independent period-split quadrature checks in 006 are accepted
- the G4 sign-flip plant is functional

The physical 006 goal and answer are immutable.

---

## Forbidden moves

- Do not change the packet coefficients.
- Do not change the definition of QW.
- Do not change the definition of `g_lambda`.
- Do not alter Fourier normalization.
- Do not fit a scalar or additive correction to the observed residual.
- Do not insert a “second edge term” merely because it closes the number.
- Do not assume the H2 pole cancels.
- Do not assume the H2 pole survives.
- Do not replace the midpoint half-weight by 0 or 1 in the canonical result.
- Do not call the absolute-tail convergence failure a proof of divergence.
- Do not hide direct, dual, edge, pole, and remainder terms inside one
  undocumented variable.
- Do not use QW positivity, RH, zero statistics, or Phase 2.
- Do not create or execute bus 008.

---

## Canonical notation

At the working cell define:

```text
D_direct
  := the exact direct observable used by bus 006

p_k
  := the signed combined Poisson contribution at index k,
     using the exact canonical c0/c4 coefficients

P_K
  := sum_{1 <= k <= K} p_k

T_K
  := sum_{k > K} p_k
     or a certified interval enclosing that signed tail

C_pole
  := the exact H2-POLE correction derived from the canonical formula

C_mid
  := the exact midpoint / half-weight correction

C_left
  := the exact already-known left-edge contribution

C_right
  := any second/right-edge contribution derived from the same identity

R_other
  := any remaining explicitly derived term
```

The target ledger is:

```text
D_direct
  =
  P_K
  + T_K
  + C_pole
  + C_mid
  + C_left
  + C_right
  + R_other.
```

Every nonzero term must be derived from an existing formula or from an exact
algebraic transformation of that formula.

If a term is zero, prove or source the zero.

---

## T0 — Input and reproduction lock

- Verify the hashes recorded by bus 006.
- Reproduce:
  - `D_direct`;
  - `P_8`;
  - `P_20`;
  - `P_40`.
- Reproduce at least one accepted independent period-split mode check.

### PASS

All reproduced values agree with bus 006 within its stated precision.

### FAILURE CODE

`INPUT_REPRODUCTION_MISMATCH`

On failure: STOP immediately.

---

## T1 — Exact formula inventory

Locate the exact formulas that define:

- the direct quantity;
- one Poisson mode;
- the finite Poisson sum;
- the lower/left endpoint;
- the upper/right endpoint;
- the midpoint half-weight;
- the H2 pole/correction;
- the truncation remainder.

Return file and line references.

For each possible correction channel assign exactly one status:

```text
PRESENT_EXACT
ZERO_EXACT
ABSENT_FROM_CURRENT_IDENTITY
UNRESOLVED
```

### Required guard

`C_right` may be called a second edge channel only if its formula is derived
before numerical evaluation.

### FAILURE CODES

```text
POISSON_LEDGER_SOURCE_MISSING
CHANNEL_FIT_FORBIDDEN
```

---

## T2 — Signed-tail analysis

Analyze the combined signed sequence `p_k`, not only the absolute mode sums.

Required:

- tabulate `p_k` for a range sufficient to expose its sign and decay pattern;
- separate mode-0, mode-4, and canonical-combination contributions;
- derive or verify the large-k decay order from the exact Legendre/Bessel
  representation;
- produce one of:
  - a certified signed-tail interval `T_K`;
  - an analytic remainder bound;
  - or an exact blocker explaining why neither is available.

Use `K = 40` as the primary ledger cutoff.

Additional cutoffs may be used only to test stability, not to replace a
missing tail theorem by brute-force extrapolation.

### Registered prediction T2-P

The absolute-tail data from 006 are compatible with convergence but do not
certify the signed tail. Therefore one of the following should occur:

```text
SIGNED_TAIL_RECOVERY:
  a certified T_40 closes the direct mismatch without a new edge channel;

SIGNED_TAIL_INSUFFICIENT:
  the certified T_40 is too small or has the wrong sign to close it;

SIGNED_TAIL_UNRESOLVED:
  no decisive certified bound is obtained.
```

### FAILURE CODES

```text
SIGNED_TAIL_BOUND_GAP
SIGNED_TAIL_ASYMPTOTIC_CONFLICT
```

---

## T3 — H2, midpoint, and edge ledger

Derive and evaluate separately:

```text
C_pole
C_mid
C_left
C_right
R_other
```

Requirements:

- `C_pole` must start from exact `h_lambda(0) != 0`.
- No cancellation may be claimed without writing the cancelling partner.
- `C_mid` must use the locked half-weight convention.
- Endpoint weights `0` and `1` may be run only as noncanonical plants.
- Preserve:
  - Fourier phase;
  - `u <-> u^(-1)` pairing;
  - integer `lambda^2 = 13`;
  - canonical c0/c4 signs.

### Registered predictions T3-P

```text
P1:
  the canonical half-weight result differs from at least one
  noncanonical endpoint plant by the expected endpoint contribution;

P2:
  the H2 correction appears explicitly in the ledger;
  whether its net contribution vanishes is decided by algebra, not assumed;

P3:
  if a genuine second edge channel exists, its derived contribution has
  the sign and scale needed to explain a material portion of the residual.
```

“Material portion” means at least 50% of the `K = 40` direct/Poisson residual.

### FAILURE CODES

```text
H2_POLE_TERM_UNACCOUNTED
H2_CANCELLATION_ASSERTED_NOT_DERIVED
MIDPOINT_CONVENTION_MISMATCH
SECOND_EDGE_FORMULA_MISSING
EDGE_PHASE_MISMATCH
```

---

## T4 — Whole-ledger closure

At `K = 40`, form:

```text
D_ledger
  :=
  P_40
  + T_40
  + C_pole
  + C_mid
  + C_left
  + C_right
  + R_other.
```

Compute:

```text
relative_closure_error
  :=
  abs(D_ledger - D_direct) / max(abs(D_direct), instrument_floor).
```

If `T_40` is an interval, propagate the interval through the full ledger.

### Numerical success threshold

`relative_closure_error <= 2e-3`

This is the original truncation-closeout target. A stronger agreement may be
reported but is not required.

### Instrument-floor guard

The absolute closure error must also be larger than neither:

`10 * independent_quadrature_error`

nor an explicitly justified high-precision arithmetic floor.

---

## T5 — Required final classification

Return exactly one primary verdict code:

```text
SIGNED_TAIL_RECOVERY
SECOND_EDGE_CHANNEL_CONFIRMED
MIXED_EDGE_AND_TAIL_RECOVERY
MIDPOINT_POLE_LEDGER_REPAIR
DIRECT_POISSON_OBJECT_MISMATCH
TAIL_BOUND_UNRESOLVED
POISSON_LEDGER_NOT_DERIVED
```

### SIGNED_TAIL_RECOVERY

- no additional edge channel is required;
- certified `T_40` closes the ledger to `<= 2e-3`.

### SECOND_EDGE_CHANNEL_CONFIRMED

- an explicit second-edge formula was derived before evaluation;
- the channel materially explains the residual;
- the complete ledger closes to `<= 2e-3`.

### MIXED_EDGE_AND_TAIL_RECOVERY

- neither signed tail nor edge alone closes the gap;
- their exact combination does;
- the complete ledger closes to `<= 2e-3`.

### MIDPOINT_POLE_LEDGER_REPAIR

- the discrepancy is accounted for by exact midpoint and/or H2-pole terms;
- no independent new edge channel remains;
- the complete ledger closes to `<= 2e-3`.

### DIRECT_POISSON_OBJECT_MISMATCH

- all derived channels and certified tails are included;
- the closure error remains `> 2e-3`;
- evidence shows the direct and Poisson sides are not the same canonical object
  or normalization.

### TAIL_BOUND_UNRESOLVED

- exact channel ledger is derived;
- the only unresolved quantity is a decisive certified signed-tail bound.

### POISSON_LEDGER_NOT_DERIVED

- the exact identity cannot be reconstructed from the available sources.

---

## Planted-failure requirements

Run all three:

### Plant A — coefficient sign

`c4 -> -c4`

Expected: the canonical closure must materially degrade.

### Plant B — midpoint convention

```text
half-weight -> 0
half-weight -> 1
```

Expected: the canonical half-weight must be distinguishable by the exact
endpoint ledger.

### Plant C — delete one derived nonzero channel

Delete the largest nonzero correction channel from the final ledger.

Expected:

`relative closure error increases by >= 5x`

or exceeds `2e-3`.

### FAILURE CODE

`RESIDUAL_LEDGER_PLANT_INERT`

---

## Required artifacts

Create exactly:

```text
bus/007_poisson_residual_channel_audit.answer.md
poisson_residual_channel_audit_v1.py
out/poisson_residual_channel_audit_v1.json
docs/PEN_3_3_POISSON_RESIDUAL_LEDGER.md
```

Do not modify the physical goal after execution starts.

---

## Required answer format

The answer file must begin exactly:

```text
# MYTHOS_PROSHKA_HANDOFF: PoissonResidualChannelAudit_v1

STATUS: STOP.
SCOPE: NOT_RH; no Phase 2; no QW/packet-definition changes; Q3 mainline untouched.
```

Then include:

```text
## Verdict
Code: <exactly one T5 verdict code>

## R1 — Input reproduction
- hashes
- reproduced values
- independent cross-check

## R2 — Exact residual ledger
- formula
- source files/lines
- status of every channel

## R3 — Signed-tail certificate
- per-mode and combined data
- asymptotic or interval bound
- T_40 result

## R4 — Pole / midpoint / edge channels
- exact formulas
- numerical values
- cancellation statements, if proved

## R5 — Whole-ledger closure
- D_direct
- P_40
- T_40
- every correction
- D_ledger
- relative closure error

## R6 — Plants
- coefficient-sign plant
- midpoint plants
- deleted-channel plant

## Mathematical implication
State only the weakest justified next implication.

## ACTIONS LOG
```

## ACTIONS LOG requirements

Record:

- every command executed;
- Python interpreter path and version;
- precision settings;
- files read;
- files created;
- files modified;
- SHA-256 for:
  - physical goal;
  - 006 answer;
  - script;
  - JSON;
  - ledger document;
  - 007 answer;
  - `ROUTE_B_STATE.md`;
- whether any cached data were reused;
- independent quadrature method and selected indices;
- `git diff --check`;
- scoped `git status --short`;
- unrelated pre-existing working-tree changes preserved;
- explicit statement:

```text
No next gate selected.
No bus 008 file created or executed.
```

## Acceptance condition

The bus goal is considered executed successfully when:

- all required artifacts exist;
- one exact T5 verdict is returned;
- the verdict follows from the displayed ledger;
- all three plants fire;
- no fitted channel or normalization is introduced;
- the answer ends in STOP.

The mathematical route need not be green.

A certified negative classification is a valid result.

---

## FINAL STEP

- Write `bus/007_poisson_residual_channel_audit.answer.md`.
- Write the JSON and pen ledger.
- Append exactly one history line to `ROUTE_B_STATE.md` containing:
  - `PoissonResidualChannelAudit_v1`;
  - the exact T5 verdict;
  - the whole-ledger closure error;
  - the signed-tail status;
  - the H2/midpoint/edge status.
- Run the required checks.
- Do not select, create, or execute bus 008.
- STOP.
