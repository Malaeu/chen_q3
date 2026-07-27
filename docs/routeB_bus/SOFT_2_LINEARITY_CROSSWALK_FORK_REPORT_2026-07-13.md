# SOFT_2 — LinearityCrosswalkFork execution report

Status: `PLANTS_LIVE / PHASE_PROBE_COMPLETE / C2_KILLED_AS_STATED / NOT_RH`

Verdict code: `C2_PHASE_FREE`.

## A. Planted-validator battery

All three validators recompute their witnesses; no stored `fired=true` flag is
trusted without replay.

| plant | witness | expected | observed | fired |
|---|---|---|---|---|
| A moving shell | `a[j,n]=1_(n=j)`; fixed `R=17,j0=23`, choose `j=24`, tail mass `1` | `SOFT_JOINT_LIMIT_QUANTIFIER_MISSING` | same | YES |
| B critical-line replacement | `2*sum_(gamma>0)H(gamma)`, not complete zero multiset | `SOFT_CRITICAL_LINE_ZERO_SUM_SMUGGLED` | same | YES |
| C grid aliasing | `J=64`, max grid value `2.1558735510086122e-14`, midpoint sup `1`, derivative scale `201.06192982974676` | `D06_GRID_ALIASING_FATAL` | same | YES |

The three clean controls pass: correct fixed-tail quantifier, complete
nontrivial-zero multiset, and a grid input with the needed uniform regularity
data are not falsely classified as the planted failures.

## B. PhaseStructureProbe

Object:

```text
H_(m,N)(x)=Xi(0) B_(m,N)(x)/B_(m,N)(0).
```

The completion Gamma/gauge factor is removed.  The grid is 4096 float64
points on `[gamma_1,gamma_11]`.  The branch-safe projective statistic uses
`exp(2i theta)`.  A sampled zero point means
`|B|<=10*eps64*max_grid|B|`, with one-neighbor dilation.  No sampled point in
these four cells met that floor; all 4096 points per cell were retained.

Before the run, the contract's qualitative `systematic drift` was fixed as a
fitted unwrapped phase excursion at least `0.3` rad with `R^2>=0.9` on a
contiguous retained segment.  The `0.3` scale is the already registered free
threshold, not a fit to the observed output.

| `(m,N)` | `sd(theta mod pi)` | axial resultant | phase slope | `slope-log(lambda)` | excursion | `R^2` | verdict |
|---|---:|---:|---:|---:|---:|---:|---|
| `(13,120)` | `0.899909670459` | `0.00959468772416` | `1.28238627476` | `-0.0000884039670` | `49.8022357135` | `0.999996778982` | `C2_PHASE_FREE` |
| `(14,120)` | `0.899158678813` | `0.0159521174639` | `1.31956193967` | `0.0000332748631` | `51.2459748294` | `0.999999356703` | `C2_PHASE_FREE` |
| `(53,120)` | `0.894244789176` | `0.0217784038076` | `2.00748760794` | `0.0223416511670` | `77.9619783916` | `0.999312874452` | `C2_PHASE_FREE` |
| `(101,120)` | `0.898724012766` | `0.0140260356478` | `2.29068001482` | `-0.0168802436030` | `88.9599243904` | `0.999486301507` | `C2_PHASE_FREE` |

Every `sd` is far above `0.3`; every cell also has systematic drift.  Hence
the registered overall result is `C2_PHASE_FREE`, not `EXTEND`.

## C. Symmetry readback

The one-page audit `SOFT_2_KTRIAL_SYMMETRY_AUDIT_2026-07-13.md` proves only

```text
kTrial real a.e.,
c_(-n)=conjugate(c_n),
B(-conjugate(z))=conjugate(B(z)),
H(-conjugate(z))=conjugate(H(z)).
```

That is conjugation symmetry.  It does not imply `H(x)` is real.  D0.1/D0.5
do not lock multiplicative inversion `k(u^-1)=k(u)` or log reflection
`g(L-x)=g(x)`.  The observed near-`log(lambda)` phase slopes are diagnostic,
not a new exact object or theorem.

Registered recoding:

```text
PHASE_SLOPE_EQUALS_LOG_LAMBDA_DIAGNOSTIC
```

Here the predicted slope is `L/2=log(lambda)`.  Its observed agreement is a
half-shift signature and a completion-gauge consistency check.  It is an
input to the V1 parity-closure question, not a parity theorem; the verdict
remains `C2_PHASE_FREE`.

## D. Fork consequence and firewalls

C2 is killed **as currently stated**.  C1 frozen-slot polarization and C3
theta/Mellin remain for the requested Proshka round-4 adjudication.  No
prime/Gamma linearity crosswalk, S2 convergence, finite roof, or RH theorem is
claimed.  All SOFT_1 RH-import firewalls remain active.  D0.7e.5a remains
`BLOCKED / ACTIVE`, its mint remains inactive, and Bus 010 is absent.

```text
C2_PHASE_FREE
```
