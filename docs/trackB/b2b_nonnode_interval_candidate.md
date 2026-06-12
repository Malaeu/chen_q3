# Track B B2b: Non-Node Interval Certificate Candidate

Status: RP4/B2 diagnostic and proof-generator contract.  This is not a
proof of E5', not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_vaaler_node_audit.md`.  The node audit
identified two receiver branches:

```text
non-node:   stay a fixed distance from Vaaler integer nodes;
node-local: split/use Taylor or series bounds near Vaaler integer nodes.
```

This card extracts the first non-node branch as a concrete interval-certificate
target.

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

Receiver variables:

```text
z_left  = delta * (a - 2K),
z_right = delta * (a - 4K).
```

No formula in this note uses the `xi` interval directly.  The cell indices and
printed intervals are raw `a` intervals.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Vaaler/Selberg sign-function construction as a standard
  Beurling--Selberg formula.
  Reference used by this track:
  https://www.math.ntnu.no/emner/MA3001/2020v/2021v/class11_zeta_NTNU.pdf
- `UNCONDITIONAL`: polygamma definitions/properties.
  Reference: https://dlmf.nist.gov/5.15
- `UNCONDITIONAL`: finite Chebyshev staircase `U_J` from
  `docs/trackB/b2b_finite_U_staircase_audit.md`.
- `UNCONDITIONAL`: elementary finite-grid Lipschitz implication:
  if `|S(a_i)| >= m`, `|S'(a)| <= L` on each mesh interval, and mesh width is
  at most `h`, then `|S|` has fixed sign when `m > L*h/2`.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Local And External Search Synthesis

Local `q3_docs` searches for interval sign certificates, FloorCert grid
guards, and Lipschitz margins again point to the existing finite-certificate
pattern:

```text
finite mesh + explicit derivative envelope + positive guard.
```

The useful local names are `FloorCert.Grid_2219`, `FloorCert.Lipschitz_2219`,
`NodeSpacing`, and the previous Track B `receiver_node_audit` fields.  No
conditional number-theory input was introduced.

External/source checks were only used to keep the Selberg--Vaaler receiver and
polygamma derivative sources explicit.  They do not add a theorem depending on
RH.

## Candidate Inequality

For a selected smooth segment define

```text
E_delta(a) = M^+_[2K,4K],delta(a) - 1_[2K,4K](a),
H_v(a) = E_delta(a) F_v(a),
S_v(a) = exp(-a/2) * (H_v'(a) - H_v(a)/2).
```

The sign-certificate target is:

```text
min_sample |S_v| > 0.5 * L_sample * mesh.
```

The diagnostic field is:

```text
allowable_LS_multiplier =
  min_sample |S_v| / (0.5 * L_sample * mesh).
```

Interpretation:

```text
allowable_LS_multiplier > 1
  means the sampled proof shape has a positive guard;

allowable_LS_multiplier <= 1
  means this segment needs root isolation, a tighter derivative bound, or a
  different split.
```

Proof gate:

```text
Replace min_sample |S_v| and L_sample by outward-rounded interval bounds for
S_v and S_v' before using the inequality as a certificate.
```

The sampled fields are only theorem-shape diagnostics.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvsigncert` now emits, per smooth
segment:

```text
non_node_interval_candidate:
  route
  status
  certificate_inequality
  sign_orientation
  sampled_min_abs_S
  sampled_L_S
  sampled_mesh
  sampled_guard
  allowable_LS_multiplier
  allowable_LS_multiplier_slack
  proof_status
```

and, per cell:

```text
non_node_interval_candidate_segment_count
non_node_min_allowable_LS_multiplier
non_node_min_allowable_LS_multiplier_slack
```

The field `status = candidate` is only allowed when:

```text
no sampled sign change,
positive sampled Lipschitz guard,
no receiver_node_audit.needs_local_node_treatment.
```

## K=3.5 Non-Node Sanity

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 801 --cells 58 59 61
```

Results:

```text
cell 58:
  recommendation: smooth_sign_cert_candidate
  node-treatment segments: 0
  non-node candidates: 1
  sign orientation: positive
  sampled guard: ~0.067381
  allowable L_S multiplier: ~1238.27
  finite U partition+jump candidate bound: ~0.197654

cell 59:
  recommendation: smooth_sign_cert_candidate
  node-treatment segments: 0
  non-node candidates: 1
  sign orientation: positive
  sampled guard: ~0.128746
  allowable L_S multiplier: ~3664.59
  finite U partition+jump candidate bound: ~0.201232

cell 61:
  recommendation: smooth_sign_cert_plus_explicit_jump_cert
  node-treatment segments: 2
  non-node candidates: 0
  smooth-side sampled guards: ~0.022040 and ~0.007145
  status: not_non_node_segment on both smooth sides
```

Interpretation:

- Cells `58` and `59` are the first theorem-producing non-node targets.
- Cell `61` remains node-local even though its smooth-side signs look stable
  numerically, because both smooth sides are too close to Vaaler integer nodes.

## K=3 Non-Node Sanity

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3 --ell 0.75 --schedule fixed --receiver-delta 0.5 \
  --p0-na 201 --ledger-cells 80 --cert-na 801 --cells 35 36 39
```

Results:

```text
cell 35:
  recommendation: smooth_sign_cert_candidate
  node-treatment segments: 0
  non-node candidates: 1
  sign orientation: negative
  sampled guard: ~0.058964
  allowable L_S multiplier: ~7919.99
  finite U partition+jump candidate bound: ~0.091893

cell 36:
  recommendation: smooth_sign_cert_candidate
  node-treatment segments: 0
  non-node candidates: 1
  sign orientation: negative
  sampled guard: ~0.048080
  allowable L_S multiplier: ~5245.40
  finite U partition+jump candidate bound: ~0.094775

cell 39:
  recommendation: isolate_roots_then_sign_certify
  node-treatment segments: 1
  non-node candidates: 0
  sampled guard: ~-2.058e-5
  allowable L_S multiplier: ~0.253
  status: not_non_node_segment
```

Interpretation:

- K=3 cells `35` and `36` are also clean non-node targets.
- K=3 cell `39` combines a root bracket with node-local receiver behavior and
  must not be routed through the non-node certificate.

## Refined Theorem-Producing Order

```text
1. K=3.5 cells 58 and 59:
   prove the non-node interval certificate using outward-rounded bounds for
   S_v and S_v'.

2. K=3 cells 35 and 36:
   repeat the same non-node certificate after the K=3.5 pilot is proof-grade.

3. K=3.5 cell 61:
   node-local Taylor/series receiver certificate plus explicit jump term.

4. K=3 cell 39:
   root isolation plus node-local receiver certificate.
```

## Verdict

`PARTIAL(non-node interval candidate contract extracted)`.

`GAP(outward-rounded interval bounds for S_v and S_v' still missing)`.

`FATAL(treating sampled min/Lipschitz guards as proof certificates)`.

Track B remains active.

Follow-up:

- `docs/trackB/b2b_nonnode_interval_stress_audit.md` measures how much
  derivative-envelope inflation the non-node candidates can tolerate before
  the sign guard fails.  K=3.5 cell `58` survives the tested `1000x` factor,
  K=3.5 cell `59` survives `2000x`, and K=3 cells `35,36` survive `5000x`;
  cells `61,39` remain outside the non-node branch.

## Proshka Audit Block

Claim:
The non-node receiver branch can be reduced to the interval inequality
`min |S_v| > L*h/2` on smooth segments.  K=3.5 cells `58,59` and K=3 cells
`35,36` are the first clean targets; K=3.5 cell `61` and K=3 cell `39` are
correctly rejected from this branch.

Point of blockage:
The current numbers are sampled diagnostics.  A proof-grade generator must
produce outward-rounded interval enclosures for `S_v` and `S_v'`, including
the Vaaler/polygamma receiver and centered B-spline packet profile.

What was tried:
Added `non_node_interval_candidate` segment fields and cell-level aggregates
to `clvsigncert`; reran K=3.5 and K=3 worklists.

Minimal example:
At K=3.5 cell `58`, the smooth segment has sampled
`min |S_v| ~ 0.067435`, `L_sample ~ 0.760447`, mesh
`~1.4323e-4`, and allowable derivative multiplier `~1238`.  Replacing these
sampled quantities by outward-rounded interval bounds would make it the first
candidate theorem.

Question for Proshka:
Should the non-node interval generator enclose `S_v` and `S_v'` directly as
product-rule expressions, or first pre-enclose the receiver derivatives
`M^+`, `(M^+)'`, `(M^+)''` and combine them with packet derivative bounds?
