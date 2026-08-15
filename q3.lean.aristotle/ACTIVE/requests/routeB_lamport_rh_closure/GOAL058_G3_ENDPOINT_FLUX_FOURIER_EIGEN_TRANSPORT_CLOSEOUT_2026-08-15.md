# Goal 058 G3 — endpoint-flux Fourier eigen-transport closeout

Date: 2026-08-15

Verdict: `G3_ENDPOINT_FLUX_FOURIER_EIGEN_TRANSPORT_PASS`

## Exact Lean result

`Q3.RouteB.D0Pstar.finiteFourierAction_preserves_prolateWaveEigenrelation_of_endpointFlux`
proves that the finite-Fourier action preserves a prolate differential
eigenrelation on the natural singular endpoint domain.

The public inputs are exactly:

1. continuity of the source on `[-lambda, lambda]`;
2. a first derivative on the open interval;
3. the divergence-form derivative equation for
   `(lambda^2-y^2) * dphi(y)` on the open interval;
4. zero-flux limits at both endpoints.

There is no global `C2` hypothesis. The output is the same prolate
differential eigenrelation for `finiteFourierAction lambda phi` at every real
argument.

## Proof boundary

The proof applies FTC to the two products
`(lambda^2-y^2) * k'(y) * phi(y)` and
`k(y) * (lambda^2-y^2) * dphi(y)`. The first boundary term vanishes from the
explicit coefficient; the second vanishes from the two supplied zero-flux
limits. The divergence-form ODE identifies the remaining bulk term.

A Tietze extension is used only to reuse the already proved
differentiation-under-the-integral formula. Equality on the closed source
window removes that extension from the final integral and from the public
interface.

This theorem proves eigenspace preservation only. It does not prove that the
Fourier image is a scalar multiple of the source mode, identify or order the
Fourier scalar, prove source zero counts, instantiate `ProlatePair`, prove CCM
Lemma 7.2, close Goal 058 G3, promote Route B, or claim RH.

## Search and validation

Fresh declared EnvDump before the write:

- source/current modules: `257/257`;
- indexed declarations: `2335`;
- stale or never-built modules: `0`;
- proof holes: `0`;
- nonstandard axioms: `0`;
- six source-less orphan oleans excluded.

Exact supplier query for finite-Fourier preservation on the endpoint-flux
domain returned `CANDIDATE_ONLY`; the old global-`C2` theorem and general FTC
lemmas were neighbors, not an exact supplier.

Checks:

- direct `lake env lean Q3/Proofs/RouteB/ProlateSourceCommutation.lean`: PASS;
- named build: PASS, `7745` jobs;
- `q3_check`: PASS;
- `git diff --check`: PASS;
- public axioms: only `propext`, `Classical.choice`, `Quot.sound`.

## Next exact seam

Derive the endpoint-domain hypotheses for the physically scaled selected
mode-zero and mode-four Ferrers witnesses, then prove restricted
finite-Fourier proportionality using ordered-mode uniqueness. Exact zero
counts and the scalar sign/order remain separate obligations.

Stop code:

`G3_ENDPOINT_FLUX_FOURIER_EIGEN_TRANSPORT_PROVED_SELECTED_FERRERS_PHYSICAL_WRAPPER_AND_SCALAR_PROPORTIONALITY_NEXT`
