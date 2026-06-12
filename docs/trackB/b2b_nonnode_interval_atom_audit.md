# Track B B2b: Non-Node Interval Atom Audit

Status: RP4/B2 proof-generator scaffold.  This is not a proof of E5', not a
proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_nonnode_analytic_curvature_audit.md`.
The previous card installed analytic formulas for `S_v''`; this card fixes
the first atom-level output contract for the future outward-rounded interval
generator.

## D2 Normalization

Raw variable:

```text
a = r * log p,
x = exp(a),
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

All intervals below are raw `a` intervals.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Vaaler's extremal-function construction.
  Source: https://www.ams.org/bull/1985-12-02/S0273-0979-1985-15349-2/
- `UNCONDITIONAL`: polygamma functions and derivative identities.
  Source: https://dlmf.nist.gov/5.15
- `UNCONDITIONAL / proof-engine style only`: directed floating-point
  neighboring by `math.nextafter`.
  Source: https://docs.python.org/3/library/math.html#math.nextafter
- `UNCONDITIONAL / local object definition`: centered cardinal B-spline packet
  profile from `q3.lean.aristotle/scripts/q3_psdpd_step13_pilot.py`, evaluated
  by the standard Cox-de-Boor centered recursion to avoid interval
  cancellation in the alternating positive-part formula.
  Reference check: https://en.wikipedia.org/wiki/B-spline

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Local And External Search Synthesis

Local `q3_docs` searches for:

```text
Track B outward rounded interval enclosure Selberg Vaaler receiver derivative
S_v curvature guard analytic product rule interval atoms
non-node Vaaler polygamma derivatives interval generator B spline packet profile
D2 edge defect CLV sign certificate mesh guard outward rounding
```

again point to the same finite-certificate pattern:

```text
grid values -> analytic derivative envelope -> mesh-cover lift.
```

No existing local note contains the missing interval atom generator.  External
source checks were kept inside the allowed input set: CLV/Vaaler, DLMF
polygamma identities, and `nextafter` as an engineering outward-neighbor
operation.  No conditional analytic number theory input was introduced.

## Atom Contract

The future certificate for each mesh interval `[a_i,a_{i+1}]` should emit
outward-rounded intervals for:

```text
E_delta, E_delta', E_delta'', E_delta'''
F_v,     F_v',     F_v'',     F_v'''
H_v,     H_v',     H_v'',     H_v'''
S_v,     S_v',     S_v''
```

where:

```text
H_v = E_delta * F_v,

S_v  = exp(-a/2) * (H_v' - H_v/2),
S_v' = exp(-a/2) * (H_v'' - H_v' + H_v/4),
S_v'' =
  exp(-a/2) *
    (H_v''' - (3/2)H_v'' + (3/4)H_v' - (1/8)H_v).
```

The mesh guard remains:

```text
lower_endpoint_abs_S
  > upper_sup_abs_S_prime_on_interval * mesh_width / 2.
```

The curvature-envelope version uses:

```text
upper_sup_abs_S_prime
  <= upper_endpoint_abs_S_prime
     + upper_sup_abs_S_second * mesh_width / 2.
```

## Probe Update

Added:

```text
scripts/trackb_nonnode_interval_atom_audit.py
```

It reuses the `clvsigncert` opnorm direction and emits the atom ranges for a
single mesh interval.  The current sampled output kind is intentionally
explicit:

```text
interval_kind = directed_rounded_sample_ranges_not_proof_grade
```

That means the script is a scaffold for the proof-producing generator.  It is
not yet a natural interval extension of the Selberg/Vaaler and B-spline
formulas.

Follow-up update: the script now also emits a natural interval extension for
the packet-profile atoms `F_v^(j)`:

```text
profile_interval_kind =
  natural_centered_b_spline_interval_with_float_coefficients
profile_interval_method =
  centered_cardinal_b_spline_cox_de_boor_recursion
profile_interval_rounding_pad = 1e-12
```

This removes the sampled-only status from the `F_v` half of the atom stack.
It is still not a Lean certificate because the current profile coefficients
and grid centers are floating pilot data.

Second follow-up update: the script now also emits interval extensions for
the Selberg/Vaaler receiver atoms and the combined product-rule atoms:

```text
receiver_interval_kind =
  vaaler_polygamma_recurrence_positive_series_tail_interval
combined_interval_kind =
  product_rule_interval_from_receiver_and_profile_atoms
```

The receiver uses recurrence to shift polygamma evaluations to the positive
half-line, then a positive series with an integral tail bound.  This follows
the DLMF polygamma identities in §5.15.  The current implementation is still a
floating interval scaffold; it is not a rational Lean certificate.

## K=3.5 Cell 58 Mesh-0 Run

Run:

```text
.venv/bin/python scripts/trackb_nonnode_interval_atom_audit.py \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 801 \
  --cell 58 --mesh-index 0 --atom-samples 65 \
  --curvature-factors 1 1000 10000
```

Target:

```text
cell = 58,
raw a cell = [6.645833333333817, 6.760416666667158],
mesh interval = [6.645833333333817, 6.645976562500484].
```

Directed sampled atom ranges:

```text
E0  in [0.5077745352436825, 0.5079942734082005]
E1  in [1.534119228790237, 1.534224550926705]
F0  in [-0.45704510276491067, -0.4563522038852088]
F1  in [4.836508256141511, 4.83887752532356]
S0  in [0.06743528530196136, 0.06754419551924461]
S1  in [0.7603350398088441, 0.760447370519764]
S2  in [-0.7880288906201764, -0.7805165716134997]
```

Node audit:

```text
min distance to Vaaler integer nodes: ~0.35402343749951637
needs local node treatment: false
```

Mesh guards:

```text
factor 1:
  derivative envelope upper: ~0.7605038048804205
  guard lower: ~0.06738082213885146

factor 1000:
  derivative envelope upper: ~0.8168817311761056
  guard lower: ~0.0673767846571506

factor 10000:
  derivative envelope upper: ~1.3247909770831796
  guard lower: ~0.06734041094813385
```

This reproduces the previous curvature-guard value for the first theorem
target, now with the atom fields named exactly as the future interval
generator should name them.

## Mesh-Density Sanity

Repeating the same mesh interval with `atom_samples` in:

```text
33, 65, 129, 257
```

gave the same directed sampled ranges for `S0` and the same factor-10000
guard:

```text
S0=[0.06743528530196136,0.06754419551924461]
S2max=0.7880288906201766
guard=0.06734041094813385
```

This is still diagnostic only.  It is useful because it says the micro-atom is
numerically stable and the future interval extension should not need an
aggressive mesh refinement at this interval.

## Profile Natural Interval Extension

Run:

```text
.venv/bin/python scripts/trackb_nonnode_interval_atom_audit.py \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 801 \
  --cell 58 --mesh-index 0 --atom-samples 65 \
  --curvature-factors 10000
```

Profile interval results:

```text
F0 interval:
  [-0.4836943690700886, -0.4297032359816557]
  width: ~0.053991133088432904
  width / sampled width: ~77.92065288323721
  contains sampled range: true

F1 interval:
  [4.724122675759641, 4.951266391331951]
  width: ~0.22714371557231064
  width / sampled width: ~95.8707931092394
  contains sampled range: true

F2 interval:
  [16.065928439553154, 17.01769190483454]
  width: ~0.9517634652813848
  width / sampled width: ~41.3931534392018
  contains sampled range: true

F3 interval:
  [-162.51851749057516, -158.55105547638678]
  width: ~3.9674620141883854
  width / sampled width: ~45.69407790205535
  contains sampled range: true
```

Interpretation:

- The direct B-spline profile atom is now a real interval extension of the
  centered-cardinal recursion over the selected raw-a interval.
- The interval is wider than the sampled range by factors `~41` to `~96`,
  but it is no longer catastrophic.  The previous naive alternating
  positive-part interval expansion showed cancellation blowup and was not the
  right proof-generator primitive.
- The remaining hard interval atoms are the Selberg/Vaaler receiver
  `E_delta^(j)` and the combined product-rule atoms `H_v^(j)`, `S_v^(j)`.

Point sanity:

```text
centered B-spline degrees tested: 0, 1, 2, 5, 8, 11
comparison target: Step13 point evaluator
result: all tested point values contained after the explicit 1e-12 pad
```

## Receiver And Combined H/S Intervals

Run:

```text
.venv/bin/python scripts/trackb_nonnode_interval_atom_audit.py \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 801 \
  --cell 58 --mesh-index 0 --atom-samples 65 \
  --curvature-factors 10000 --polygamma-tail-terms 400
```

Receiver interval results:

```text
E0 interval:
  [0.5072671903595878, 0.5085018132801803]
  width: ~0.0012346229205925099
  width / sampled width: ~5.6186094177181545
  contains sampled range: true

E1 interval:
  [1.5291157135485514, 1.5392303908409253]
  width: ~0.010114677292373921
  width / sampled width: ~96.03562585772502
  contains sampled range: true

E2 interval:
  [0.6748395753149601, 0.7958203605066858]
  width: ~0.12098078519172574
  width / sampled width: ~64.4295061910666
  contains sampled range: true

E3 interval:
  [-14.27906023114253, -11.940698738206887]
  width: ~2.3383614929356438
  width / sampled width: ~965.4499638991621
  contains sampled range: true
```

Combined product-rule interval results:

```text
S0 interval:
  [0.06347021663883491, 0.07150540275891909]
  width: ~0.00803518612008418
  contains sampled range: true
  excludes zero: true

S1 interval:
  [0.7313555591886495, 0.7894215401009012]
  width: ~0.05806598091225169
  contains sampled range: true

S2 interval:
  [-1.0233364325665644, -0.5410266033854875]
  width: ~0.48230982918107695
  contains sampled range: true
```

The local interval sign guard now passes directly:

```text
S0_abs_lower: ~0.0634702166388349
S1_abs_upper: ~0.7894215401009013
mesh_width_upper: ~0.00014322916666653643
direct S1 mesh guard lower: ~0.06341368254416625
curvature S2 mesh guard lower: ~0.06341367729583335
```

Tail-term sanity:

```text
polygamma tail terms = 100:
  E0_width ~0.0012490909414788478
  E3_width ~2.340145677747753
  direct guard ~0.06341200051108943

polygamma tail terms = 400:
  E0_width ~0.0012346229205925099
  E3_width ~2.3383614929356438
  direct guard ~0.06341368254416625

polygamma tail terms = 1000:
  E0_width ~0.0012337801640212034
  E3_width ~2.338258134976979
  direct guard ~0.0634137804410493
```

Interpretation:

- K=3.5 cell `58`, mesh interval `0`, now has a local interval sign guard
  using receiver/profile/product-rule intervals rather than sampled `S`
  values.
- The interval is still a floating scaffold.  The proof-producing version
  must rationalize constants, packet coefficients/centers, and the receiver
  tail bounds, then repeat this over all mesh intervals in the cell.
- The next live task is not another formula rewrite for this mesh interval;
  it is a worklist lift: run the same interval guard over all `800` mesh
  intervals of cell `58`, identify the weakest intervals, and only then decide
  whether Proshka should attack rationalization or interval tightening first.

## Verdict

`PARTIAL(local combined interval sign guard installed for K=3.5 cell 58 mesh 0)`.

`GAP(full-cell worklist lift, rational certificate data, and Lean-grade
outward rounding still missing)`.

`FATAL(treating the floating interval scaffold as a proof-grade E5'
certificate)`.

Track B remains active.

## Proshka Audit Block

Claim:
The first non-node theorem target now has a local combined interval sign guard
for `S_v` on K=3.5 cell `58`, mesh interval `0`.

Point of blockage:
The current guard is a floating interval scaffold over one mesh interval.
It is not yet lifted to all `800` mesh intervals of the cell, and it is not
rationalized into Lean-grade certificate data.

What was tried:
Added `scripts/trackb_nonnode_interval_atom_audit.py`, reused the
`clvsigncert` opnorm direction, and checked K=3.5 cell `58`, mesh interval
`0`, with `atom_samples` up to `257`.  Then replaced the profile interval
primitive by a centered-cardinal B-spline recursion interval with a `1e-12`
rounding pad.  Then added Selberg/Vaaler receiver intervals using polygamma
recurrence plus positive-series tail bounds and combined them into `H/S`
intervals by product rule.

Minimal example:
K=3.5 cell `58`, mesh interval
`[6.645833333333817, 6.645976562500484]` has combined
`S0=[0.06347021663883491, 0.07150540275891909]`; it excludes zero and gives
direct mesh guard `~0.06341368254416625`.

Question for Proshka:
After the full-cell worklist is generated, should rationalization start from
separate receiver/profile atoms, or from already-combined `S_v`, `S_v'`,
`S_v''` interval records?
