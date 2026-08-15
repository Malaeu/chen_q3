# Goal 058 G3 — physical Ferrers Fourier eigen-transport closeout

Date: 2026-08-15

Verdict: `G3_PHYSICAL_FERRERS_FOURIER_EIGEN_TRANSPORT_PASS`

## Exact Lean result

The new module
`Q3/Proofs/RouteB/D0Mode4FerrersPhysicalFourierEigenTransport.lean`
exports the complexified physical Ferrers source and proves:

`Mode4FerrersRegularEvenProlateSolution.physicalFiniteFourierAction_preservesProlateWaveEigenrelation`.

For any already accepted regular even Ferrers witness `S` and only the
production size hypothesis `2 <= mProject`, its finite-Fourier image at
`lambda = sqrt(mProject)` satisfies the same prolate differential
eigenrelation with eigenvalue
`Lambda + mode4JacobiG mProject` at every real argument.

The public theorem takes no Fourier eigenrelation, scalar, zero count, global
smoothness, or new source-existence binder as an input.

## Transported facts

The module proves separately:

1. complex physical continuity on the exact closed window;
2. the actual complex first derivative on the open window;
3. the complex divergence-form flux derivative from the accepted physical
   second derivative and exact ODE;
4. both physical complex zero-flux limits under
   `u -> u / sqrt(mProject)`;
5. the final application of the generic endpoint-domain Fourier theorem.

The scale and potential remain literal:

- `lambda = sqrt(mProject)`;
- `theta = Lambda + mode4JacobiG mProject`;
- potential `(2*pi*sqrt(mProject)*u)^2`.

## Search and validation

Fresh declared EnvDump before the write:

- current modules: `257/257`;
- declarations: `2336`;
- stale or never-built modules: `0`;
- proof holes: `0`;
- nonstandard axioms: `0`.

The exact physical-wrapper supplier query returned `CANDIDATE_ONLY`.

Checks:

- direct Lean: PASS;
- named build: PASS, `7775` jobs;
- `q3_check`: PASS;
- diff check: PASS;
- every public declaration uses only `propext`, `Classical.choice`,
  `Quot.sound`.

## Boundary and next seam

This proves only that the Fourier image stays in the same differential
eigenspace. It does not prove proportionality to the source mode. The next
honest seam is a source-faithful uniqueness/proportionality theorem for the
selected even regular mode; exact zero counts may be required to identify the
ordered mode. Fourier scalar sign/order, orthogonality, `ProlatePair`, CCM
Lemma 7.2, denominator floor, schedule, G1, and G3 remain open.

Stop code:

`G3_SELECTED_PHYSICAL_FERRERS_FOURIER_ODE_TRANSPORT_PROVED_SCALAR_PROPORTIONALITY_AND_NODAL_SELECTION_NEXT`
