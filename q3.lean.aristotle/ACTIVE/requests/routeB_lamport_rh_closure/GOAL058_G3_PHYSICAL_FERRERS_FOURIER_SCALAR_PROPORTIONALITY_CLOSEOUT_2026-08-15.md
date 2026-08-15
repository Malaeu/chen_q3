# Goal 058 G3 — physical Ferrers Fourier scalar proportionality closeout

Date: 2026-08-15

Verdict: `G3_PHYSICAL_FERRERS_FOURIER_SCALAR_PROPORTIONALITY_PASS`

## Exact Lean result

The new module
`Q3/Proofs/RouteB/D0Mode4FerrersPhysicalFourierScalarProportionality.lean`
proves:

`Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_scalar_mul`.

For every accepted regular even Ferrers witness `S`, with only
`2 <= mProject`, it constructs `chi : Complex` such that

`finiteFourierAction (sqrt mProject) h x = chi * h x`

for every `x` in the exact closed physical window
`[-sqrt mProject, sqrt mProject]`, where `h` is the already accepted
complexified physical Ferrers series.

No Fourier scalar, scalar relation, zero count, global smoothness, or new
source-existence binder is taken as an input.

## Proof architecture

The module materializes the following exact chain:

1. complex divergence-form prolate ODE uniqueness from center Cauchy data;
2. differentiation of the finite-Fourier integral from continuity only on the
   actual compact source window;
3. literal first- and second-derivative Fourier integrals;
4. evenness of the finite-Fourier action of an even source;
5. vanishing of both center derivatives by evenness;
6. nonvanishing of the physical source at the center from the accepted
   `center_value_ne_zero` theorem;
7. `chi := Fh(0) / h(0)` and ODE uniqueness on the open window;
8. continuity closure from the open window to the exact closed window.

The result did not require an interior zero count or a new ordered-mode
selection hypothesis. The selected mode-zero/mode-four witnesses constructed
earlier can consume this theorem directly.

## Search and validation

Fresh declared EnvDump before the write:

- current modules: `258/258`;
- declarations: `2345`;
- stale or never-built modules: `0`;
- proof holes: `0`;
- nonstandard axioms: `0`;
- six source-less orphan oleans excluded fail-closed.

The exact supplier query for complex prolate IVP uniqueness, even-source
Fourier center derivative, and scalar proportionality returned
`CANDIDATE_ONLY`.

Checks:

- direct Lean: PASS;
- named build: PASS, `7779` jobs;
- `q3_check`: PASS;
- diff/forbidden scan: PASS;
- every public declaration uses only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Boundary and next seam

The constructed scalar is currently complex-valued. This leaf does not prove
that it is real, nonzero, positive, or ordered between the selected mode-zero
and mode-four witnesses. It also does not prove orthogonality, instantiate the
production `ProlatePair`, prove CCM Lemma 7.2, establish the denominator floor
or schedule, close G1/G3, promote Route B, or make an RH claim.

Next exact seam: exploit the real-even source and finite-Fourier
nonvanishing/primary spectral order to obtain the source-normalized real
nonzero scalar data needed by `ProlatePair`.

Stop code:

`G3_SELECTED_PHYSICAL_FERRERS_RESTRICTED_FOURIER_PROPORTIONALITY_PROVED_SCALAR_REAL_NONZERO_SIGN_ORDER_AND_PROLATEPAIR_NEXT`
