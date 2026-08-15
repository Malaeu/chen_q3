# Goal 058 G3 — physical Ferrers Fourier nonzero scalar closeout

Date: 2026-08-15

Verdict: `G3_PHYSICAL_FERRERS_FOURIER_NONZERO_SCALAR_PASS`

## Exact Lean result

The new module
`Q3/Proofs/RouteB/D0Mode4FerrersPhysicalFourierNonzeroScalar.lean`
proves

`Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul`.

For every accepted regular even Ferrers witness `S`, with only
`2 <= mProject`, it constructs `chi : Real` with `chi != 0` and

`finiteFourierAction (sqrt mProject) h x = (chi : Complex) * h x`

for every `x` in the exact closed physical window.

## Proof architecture

The module first defines `finiteFourierEntire`, the literal complex-frequency
extension of the compact-window Fourier integral.  Differentiation under the
integral proves that this extension is entire, and an exact bridge identifies
its real-axis values with the project `finiteFourierAction`.

If the finite-Fourier action vanished throughout the open source window, the
analytic identity theorem would make the entire extension zero everywhere.
The existing Fourier-inversion theorem
`finiteFourierAction_ne_zero_of_integrableOn_continuousAt` contradicts that
for a continuous source with a nonzero interior value.  The accepted physical
Ferrers source has exactly such a nonzero value at the center.  Therefore the
already-proved real proportionality scalar cannot be zero.

## Search and validation

Declared full EnvDump before the production write:

- current modules: `260/260`;
- declarations: `2354`;
- stale or never-built modules: `0`;
- proof holes: `0`;
- nonstandard dependencies: `0`;
- six source-less orphan oleans excluded fail-closed.

The exact supplier preflight returned `CANDIDATE_ONLY` on that complete
environment.

Checks:

- direct Lean: PASS;
- named build: PASS, `7782` jobs;
- `q3_check`: PASS;
- diff/forbidden scan: PASS;
- all public declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Boundary and next seam

This leaf proves realness and nonvanishing, but not the scalar sign or the
ordering between the selected mode-zero and mode-four scalars.  It does not
instantiate `ProlatePair`, prove orthogonality, the CCM floor, schedule, close
G1/G3, promote Route B, or make an RH claim.

Next exact seam: source-locked spectral index/sign/order identification for
the positive-phase finite Fourier operator, followed by zero extension,
normalization, orthogonality, and production `ProlatePair` assembly.

Stop code:

`G3_SELECTED_PHYSICAL_FERRERS_RESTRICTED_FOURIER_REAL_NONZERO_SCALAR_PROVED_SIGN_ORDER_AND_PROLATEPAIR_NEXT`
