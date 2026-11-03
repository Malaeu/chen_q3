# Uniform old-history extension margins

DIAGNOSTIC_NEVER_A_PROOF. CHALLENGER / NOT_RH. No route-state edit.

The saved scalar innovations determine the **one-new-endpoint** margin exactly:
for n old increments and a new step Delta, mu=innovation_(n+1)/[2Psi(Delta)].
`single_endpoint.csv` contains 8,628 rows across four meshes and three worlds.
Only positive old histories are interpreted as margins; all subsequent rows
are marked invalid. At the first negative extension the old history is still
positive and the margin is negative. This agrees in crossing sign with the
planted negative-capacity threshold; the two margins have different
normalizations and generally different numerical values.

For an entire sampled future we use q equal fresh increments over delta.
With their fresh Gram F and old/new Gram B, the canonical-correlation margin
is 1-lambda_max(F^(-1/2) B^T C^(-1) B F^(-1/2)). This has the same nonzero
spectrum as the old-whitened expression in the brief. The Cholesky transform
is applied to every old increment. No old modes or arithmetic atoms are
removed. Both C and F must be positive. This is a finite restriction of the
full short-source operator: when that operator is positive, nested fresh
test spaces produce decreasing margins. A positive finite sampled margin
is an **upper approximant**, not a positive lower bound for all future nodes.

## Future-node refinement at a=6, delta=Delta

| Old mesh | q=1 | q=32 | q=128 |
|---|---:|---:|---:|
|1/32|0.192005211|0.087489910|0.087061794|
|1/64|0.190036790|0.103996401|0.103702040|
|1/128|0.191119553|0.133065626|0.132832070|
|1/256|0.215579926|0.160093482|0.159902345|

The one-endpoint value near .2 is not the all-new-node margin. Future
refinement changes the coarse result by more than a factor of two.
The registered finite sampled .1-floor claim fails at a=6 on mesh32;
this is beyond log240, so it does not settle Mythos's arithmetic-section
claim. The largest q32-to128 absolute change is .000428116. No extrapolated
infinite-q value or rigorous discretization error is claimed.

`future_refinement.csv` contains 480 rows, including pre-onset controls;
185 rows with indefinite past are explicitly invalid, and no numerical
factorization failure occurred in the other rows. Every tested nested
future refinement was nonincreasing within the 1e-8 numerical guard.
`extended_refinement.csv` records the eight q64/q128 additions separately.

## Step search uses a genuinely nested future grid

For zeta after a=1,3,6, the fresh microstep is fixed at Delta/4; larger
delta adds future nodes without moving the old nodes or previous future
nodes. Every tested block stays positive to delta=1/4 on every old mesh.
At a=6, old mesh1/256, mu decreases from .559386 at the first microstep to
.167085 at delta=Delta, .00416375 at delta=1/32, .00106740 at1/16,
.000292236 at1/8 and .0000966932 at1/4.

Thus no finite failure step is detected within this cap. This gives only
`delta_star_sampled >= 1/4` on those finite node sets. It gives no lower
bound on the exact all-node delta_star. Under RH, the source kernel is
positive on the entire half-line and its actual admissible step supremum
is infinite; a finite decreasing zeta delta_star is not a consequence of
RH. A search over one moving endpoint would not answer the all-node problem.

## Precision and reproduction

Vectorized float64 source evaluation uses all integer coefficients below
exp(6.3), exact hinge locations, the full dilogarithmic arch term and both
zeta poles. DH uses its own coefficients/gamma constant and no pole; the
plant uses gamma=2pi/log2, eta=1/4, multiplicity1. The old covariance r
samples come from the committed MP100 source data. Selected source values
agree with separate MP80 evaluations to at most1.13e-13 absolute.

`mp_validation.json` independently replays six blocks using MP80 dense
Cholesky, with one MP120 repeat. The old r inputs carry100digits, even in
the120digit repeat. Maximum margin discrepancy from float64 is1.30e-13.
This includes the coarse a6,q32 result below.1, the coarse delta1/4 block,
a negative planted extension and DH/fine-mesh normalization controls.
The larger q128 refinements remain floating diagnostics, not interval
certificates. No lower bound on the infinite operator follows from them.

Run from this directory in the repository (restore innovation data first):

```
uv run --with mpmath --with numpy --with scipy python margins.py
uv run --with mpmath --with numpy --with scipy python refine.py
uv run --with mpmath --with numpy --with scipy python validate.py
python analyze.py
```

The preregistration records probabilities and kill-switches before each
run. SUMMARY.json contains counts, refinement checks and validation maxima.
