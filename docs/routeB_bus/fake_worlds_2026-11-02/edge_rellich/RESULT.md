# EDGE_LAW_RELLICH_v1

**DIAGNOSTIC_NEVER_A_PROOF. Route B: CHALLENGER / NOT_RH.**

The dilation boundary-only prediction fails on the eight requested zeta
cells under both explicit boundary definitions tested here. No new
explanatory generator or cofinal edge law is established. The useful
outcome is an exact distinction between complement leakage, finite Green
boundary, and physical weak dilation; these cannot be substituted for one
another. All numerical work uses the saved directions, without a new
eigenproblem or optimizing a generator to the answer.

Input base: `rh_clean @ 05c177921c8c3f88eef958875f949f0dab691d94`.
The eight zeta cells are m55/q27, m80/q41, m120/q63,q64,q65,
m160/q89, m200/q115 and m240/q139. Thirteen DH controls retain native
kappa=1.1 and matched constraint counts, including both DH120 brackets.
The q64 DH density match is impossible without splitting a quartet and
is not manufactured. `INPUTS.json` pins all 23 input blobs and byte hashes.

## (i) Which commutator was computed

For the literal finite A_m, the literal diagnostic object is
`C=<f,[A_m,D_m]f>`, with `D_m=P_m(x partial_x+1/2)P_m` in the physical
orthonormal even carrier. Its natural Green identity is

    C = V-B,
    V = 2<Af,D_m f>,       B = L f(b)(A_m f)(b).

All saved f have f'(b)=0 EXACTLY, while f(b) is generally nonzero.
No first-order Green term containing f'(b) is missing. Since A is nonlocal,
its finite boundary contains the synthesized trace (A_m f)(b); it is not
a local-Laplacian boundary determined only by f(b),f'(b).

For a complement ground, Af=lambda f+r, r in J up to inherited numerical
residuals. With K=(D_m-D_m^T)/2,

    C=2<r,Kf>.

The lambda L f(b)² pieces in V and B cancel. Thus C measures leakage from
J-perp, and need not be zero for a complement ground. If A and D are both
compressed to J-perp, the expectation is exactly zero at its eigenvector.
This does not rule out a future source-specific Rellich identity with
additional energy and boundary terms; no such identity is supplied here.

The physical zero-extended f is outside the global L² dilation domain when
f(b)!=0. Therefore a second, explicitly different object is also evaluated:
`W=2q(f,D_int f)`, with D_int f formed INSIDE the window and then
zero-extended. Its Fourier transform is

    H(z)=L f(b)cos(bz)-F(z)/2-zF'(z).

W has its own full source boundary/volume split. The projection-return
`W-V=2q(f,(I-P_m)D_int f)` is reported and not discarded.
Definitions and derivations of every component are in `FORMULAS.md`.

`summary.csv` records V, B, C, W, Bweak, Vweak, the projection-return,
f(b), exact f'(b)=0, lambda and the alternative generator for all 21 cells.
`TABLE.md` gives a compact comparison. Full precision outputs, component
ledgers, numerical residuals and individual DH quartets are in `cells/`.

## Zero head and tail

Every cell separately reports the actual supplied zero head gamma<=T and
the finite prefix T<gamma<=400 (zeta) or <=310 (DH). Finite Green V/B and
combined weak W are independently evaluated on those nodes. Signed DH
quartets use 4Re(F²) for energy and 8Re(FH) for weak variation; positive
absolute-value squares would be the wrong metric.

`zero_sides.csv` records those heads/prefixes and two EXPLICIT SOURCE
BALANCES: source minus head, and source minus head/prefix. Neither is an
independently summed or certified infinite zero tail. Unknown zeros are
not assumed real, absent, or positive. Census and multiplicity
qualifications remain those of the pinned numerical datasets.

There is an additional boundary-tail obstruction: splitting H into
`Lfb cos(bz)` and `-F/2-zF'` produces separated zero summands with only
O(1/t) decay. They are not absolutely summable against zero density.
The finite boundary/volume prefixes are unambiguous, but their separate
infinite tails have NO canonical value here without regularization.
Only combined weak W receives a source balance. The source split Bweak/Vweak
is not misrepresented as two independently converged infinite zero sums.

## (ii) The preregistered 10% test

Owner prediction: p=0.35 that a boundary term explains lambda within 10%.
No fitted coefficient is used. With the conventions fixed before running,
the tests are |B-lambda|/|lambda|<=0.1 and
|Bweak-lambda|/|lambda|<=0.1; the opposite sign -B is also retained to
make the subtraction convention explicit.

For zeta, neither B nor -B nor Bweak passes on any of the eight cells.
For example, at m120/q64,

    lambda = 6.134500659e-10,
    C      = 4.4886337e-8,
    B/lambda     = 1.4884798e-5,
    Bweak/lambda = 60.315297.

At m240, B/lambda is about 9.85e-16 while Bweak/lambda is about -62.51.
The boundary-only explanation therefore fails at this finite diagnostic
scope. It is not repaired by identifying the finite C with lambda or by
silently deleting the physical projection-return.

## (iii) DH: what changes

Native DH directions are almost full-carrier negative directions in these
saved cells: their dilation commutators are tiny, despite nonzero negative
lambda. Matched constraints can produce a substantial residual r and a
large leakage commutator. At m120 the native C is about 8.7e-16;
matched q63/q65 have C about -8.68/-5.93 with lambda about -1.55.
Small C alone would not imply small r; the output also retains ||r||.

This is consistent with the algebraic leakage formula, not a boundary
floor theorem. The zero-side decomposition also retains the indefinite
complex metric, including the quartet near gamma=240.405 in native240.
Individual quartet entries are included in each cell so a switch of
direction is not hidden inside a positive Gram or a single first quartet.
Native and matched cutoffs are not treated as the same space.

## (iv) Initial bounded freedom

The initial additional generator is
`D_a=a(x) partial_x+a'(x)/2`, `a=x(1-x²/b²)`.
It preserves parity, vanishes at both endpoints, and its projected matrix
is skew. Thus it repairs the boundary-domain issue; its Green boundary is
exactly zero. The computed expectation still measures leakage,
`<f,[A,D_a]f>=2<r,D_a f>`, and gives no automatic boundary-only lambda law.

No generator fitted to A, f or lambda was introduced. The subsequent owner steering adds the prolate test below. Budget is closed
after the 21 saved vectors, the two explicit auxiliary generators, independent
spatial controls and three refinements. A genuinely explanatory nonlocal
source-specific commutator remains research debt. This is not a no-go
for every possible generator. Hypothesis/evidence/falsifier/handoff cards
and the scoped kill-switch are in `HYPOTHESES.md`; nothing was sent to Proshka.

## Owner clarification: primary weak layer, K1 and prolate

The owner's later clarification fixes the literal layer as K1 only and
makes the weak source layer primary. `STEERING.json` and
`weak_four_pieces.csv` report, on every requested vector:

- K1: ||r||, 2Re<r,D_m f>, the rank-one defect D_m+D_m^T and its
  f/f and r/f contractions. Its operator norm is 2m+1, so D_m is not
  silently treated as skew.
- Four weak pieces: arch volume, arithmetic volume, pole volume and the
  complete jump/scalar/Green defect. Their sum is W=2q(f,D_int f).
- The separately requested log-weighted arithmetic Q probe. For dilation
  the exact arithmetic volume uses Q', not Q. The remaining derivative
  cannot be dropped after [x,T_s]=-sT_s. No favorable conclusion is based
  on substituting the Q probe for that commutator.

All 15 nonempty unweighted subsets of the four signed pieces were tested
with the SAME subset on all eight zeta cells. None passes 10% relative to
lambda, and none passes relative to 4*fb²log(T)/(pi*T). No fitted
coefficient or cell-dependent selection was used. This follow-up comparison
was registered after the steering and is not advertised as blind to the
initial boundary measurements. The complete per-subset errors are retained.

For the requested prolate fallback, use exactly
`Wpro=-partial_x((b²-x²)partial_x)`, without the optional potential.
Its Galerkin matrix is real symmetric, hence its finite real-vector
commutator expectation is EXACTLY zero, source-by-source. The symmetric
weak-form difference is also zero. These are algebraic zeros, not tiny
computed nonzero eigenvalues.

The interior maximal-differential-expression interpretation is different:
near x=b-h, A_arch f=(fb/2)log(1/h)+O(1), and
`(b²-x²)(A_arch f)' -> b fb`. The opposite endpoint has flux -b fb.
Consequently its arch commutator has the exact endpoint anomaly

    <f,A_arch Wpro f - Wpro_max A_arch f> = L fb².

The outer distribution/Green defect is -Lfb². For a shifted arithmetic
atom -w(T_s+T_-s), the regular prolate volume is
`+2w fb (b²-(b-s)²) f'(b-s)` and its shifted delta-prime contribution
is the negative. Both are retained in `weak_four_pieces.csv`; deleting
those interior jumps would produce a spurious arithmetic signal. Pole and
scalar prolate commutators are zero. The combined form bookkeeping is zero.

Thus the prolate test does identify an honest Dirichlet-trace anomaly,
but not the requested edge law. Rescaling Lfb² by log(T)/(pi*T*L) would
INSERT the observed edge scale, rather than derive it. The coefficient
near four and its source/zero remainder remain unpaid. `FORMULAS.md`
gives the distinction, and `PROLATE_VALIDATION.json` independently checks
the modal projection, a shifted atom with both jump terms, and the endpoint
kernel limit. No new eigenproblem was used.

All requested m are composite non-prime-powers and divisible by five;
their birth coefficient b(m) is exactly zero in both worlds. The replay
code nevertheless retains n=m in the weak split: in general its one-sided
volume and jump pieces cancel rather than being discarded separately.

## Validation and replay

Baseline: 110 dps, 8-panel GL192 source integration. Fixed-vector controls
use 140 dps/GL256 on zeta55, zeta240 and native DH240. Saved vectors and
zero precision are not promoted by increasing arithmetic precision.
`VALIDATION.json` records source-Rayleigh replay errors, direct/leakage
commutator agreement, Green/skew residuals and refinement differences.

`FORMULA_VALIDATION.json` comes from independent small-carrier spatial
integrals for D_m, the alternative generator, H(z), and the mixed
correlation formula. Their errors are below 3e-80 at 80 dps. No actual
zero or CCM eigenvalue is assigned in those controls. The formulas and
domain distinction also received a bounded independent read-only review.
These are numerical/algebraic controls, not interval certificates.

From this directory in a repository containing the pinned base objects:

    python materialize_inputs.py --repo /path/to/repo --out ./inputs
    python rellich.py ./inputs 192
    python refine.py ./inputs
    python check_formulas.py > FORMULA_VALIDATION.json
    python summarize.py
    python steering.py ./inputs
    python check_prolate.py > PROLATE_VALIDATION.json

Python plus mpmath suffice. `SHA256SUMS` covers committed artifacts;
`INPUTS.json` covers the unduplicated original inputs. No new CCM spectrum,
zero census, route-state write, RH export, cofinal lower bound or proof
claim is made.
