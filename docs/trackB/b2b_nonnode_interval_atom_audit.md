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
single mesh interval.  The current output kind is intentionally explicit:

```text
interval_kind = directed_rounded_sample_ranges_not_proof_grade
```

That means the script is a scaffold for the proof-producing generator.  It is
not yet a natural interval extension of the Selberg/Vaaler and B-spline
formulas.

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

## Verdict

`PARTIAL(atom-level certificate contract emitted for K=3.5 cell 58 mesh 0)`.

`GAP(natural interval extensions for Selberg/Vaaler receiver and B-spline
profile atoms still missing)`.

`FATAL(treating directed sampled ranges as proof-grade interval enclosures)`.

Track B remains active.

## Proshka Audit Block

Claim:
The first non-node theorem target can now be expressed as an atom-level
certificate over one raw-a mesh interval: `E_delta^(j)`, `F_v^(j)`,
`H_v^(j)`, and `S_v^(j)` for `j <= 3` / `j <= 2` as appropriate.

Point of blockage:
The current script emits directed-rounded sampled ranges.  It does not yet
evaluate the Vaaler/polygamma receiver and B-spline profile by natural
outward-rounded interval extension.

What was tried:
Added `scripts/trackb_nonnode_interval_atom_audit.py`, reused the
`clvsigncert` opnorm direction, and checked K=3.5 cell `58`, mesh interval
`0`, with `atom_samples` up to `257`.

Minimal example:
K=3.5 cell `58`, mesh interval
`[6.645833333333817, 6.645976562500484]` has
`S0=[0.06743528530196136,0.06754419551924461]` and factor-10000 guard
`~0.06734041094813385` under the directed sampled atom scaffold.

Question for Proshka:
Should the proof-producing generator first intervalize the receiver atom
`E_delta^(j)` and profile atom `F_v^(j)` separately, then combine them into
`H/S`, or directly intervalize the full product-rule expression for `S_v`,
`S_v'`, and `S_v''`?
