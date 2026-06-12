# Step33A.1-A Endpoint v18 First-Row Proof Pack

Status: prepared for Aristotle/local proof work, not submitted.

## Target Lean File

```text
q3.lean.aristotle/aristotle_input/step33_endpoint_v18_first_row_pilot.lean
```

This file imports the real checked endpoint rational layer:

```lean
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointRationalImport
```

It has exactly two intentional proof holes:

```lean
primaryFiniteRow0Parent0Split100Sub0OmegaEndpointBounds_aristotle_v18
primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_aristotle_v18
```

Once those two are proved, the local combiner is already checked:

```lean
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_aristotle_v18
```

## Concrete Row

```text
family: primary_finite
row: 0
parentChunk: 0
split: 100
subchunk: 0
k: 11
ell: 3/10
a: 499999999999999999999/10000000000000000000000
b: 1/20
anchor: 1/20
etaRadius: 1/10000000000000000000000
```

Decimal view:

```text
a ~= 0.0499999999999999999999
b = anchor = 0.05
etaRadius = 1e-22
```

## Already Checked Locally

The generated rational containment theorem is already checked in:

```lean
primaryFiniteRow0Parent0Split100Sub0EndpointRationalCert_generated
```

and the generated combiner is already checked:

```lean
primaryFiniteRow0Parent0Split100Sub0EndpointIntervalCert_of_endpoint_bounds_generated
```

So the proof task is not endpoint-radius arithmetic.

The already checked containment margins for this row are:

```text
Omega containment:
  consumed ~= 2.377589248047366793771794896001e-22
  radius   ~= 2.487199989833435045049250024048e-21
  margin   ~= 2.249441065028698365672070534448e-21

ShapeSq containment:
  consumed ~= 2.224892420717738982528107838981e-26
  radius   ~= 2.853844396041518697286715880093e-20
  margin   ~= 2.853842171149097979547733351985e-20
```

## Omega Proof Route

Preferred receiver:

```lean
Step22OmegaClosedFormEndpointBoundsCert
  .of_re_series_anchor_trigamma_im_closed_form_term_prefix_cubic_tail_Icc
```

It expects:

```text
derivN, anchorN
termLower/termUpper for trigammaImSeriesTermClosedForm
imPrefixLower/imPrefixUpper
cubic tail sum bound
derivative lower/upper rational comparisons
anchor const/prefix/tail bounds for the direct Step22 Omega re-series
anchor lower/upper rational comparisons
```

Target endpoint values for this row:

```text
omegaDerivLower ~= 1.5850595290666072382126312834178921152264801346872
omegaDerivUpper ~= 1.5850595290666072382158324731584005758239400084074
omegaAnchorLower ~= -5.3321646763652276295910643695980703772497139811870
omegaAnchorUpper ~= -5.3321646763652276295910643695980703772497139811870
```

The anchor interval is padded by `2e-80`, so do not try to prove exact
transcendental equality.

## ShapeSq Proof Route

Preferred receiver:

```lean
primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_of_value_deriv_bounds_generated
```

It expects:

```text
E lower/upper interval on [a,b]
E' closed-form lower/upper interval on [a,b]
tight lower/upper endpoint facts for E(anchor)^2
```

The generated helper already closes the concrete rational corner comparisons
for `2 * E * E'`.  Do not use the full-subchunk `E` interval to derive the
tight `E(anchor)^2` target: those anchor-corner comparisons are false for the
current tight endpoint constants.  Prove the two shape-square anchor facts
directly.

Target endpoint values for this row:

```text
shapeValueLower ~= 0.77106532600497004327829058130608653834672980191509
shapeValueUpper ~= 0.77106532600497004331530228803943470252057742869432
shapeDerivLower ~= -0.000096383175790535848472188253270568180656541745809029
shapeDerivUpper ~= -0.000096383175790535848467754561681043747644715086353592
shapeSqDerivLower ~= -0.00014863544972464772055087959091330496796120686361465
shapeSqDerivUpper ~= -0.00014863544972464772053690764753876455557388747430966
shapeSqAnchorLower ~= 0.59454173696715073210978160925817253868988574837787
shapeSqAnchorUpper ~= 0.59454173696715073210978160925817253868988574837787
```

The active route is the corrected `E/E'` route through the generated helper.
Do not use the older direct `E^2` derivative probe; the worklist marks that
probe as audit-only and not contained for this row.

## Validation Commands

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle
lake env lean aristotle_input/step33_endpoint_v18_first_row_pilot.lean
```

Expected current result before Aristotle:

```text
Lean compiles.
There are exactly two `sorry` warnings, corresponding to the two target
endpoint packages above.
```

## Submit Command After Explicit User OK

Use the context bundle route.  The single-file `aristotle formalize ...lean`
route is not preferred for this pilot because the proof depends on real Q3
imports and checked endpoint receivers.

```bash
cd /Users/emalam/Documents/GitHub/rh_lean_01_2026
python3 q3.lean.aristotle/scripts/q3_psdpd_step33_endpoint_first_row_context_bundle.py
source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate
aristotle submit "Fill the two intentional endpoint proof holes in aristotle_input/step33_endpoint_v18_first_row_pilot.lean. Use the checked Q3 receivers named in aristotle_input/step33_endpoint_v18_first_row_proof_pack.md; do not add axioms, unsafe code, trusted numerical black boxes, admit, exact?, or theorem weakening. Return hole-free Lean proof replacements or the exact missing analytic lemma." --project-dir /tmp/q3_step33_endpoint_v18_first_row_context
```

Do not submit without explicit user OK under the Aristotle workflow.
