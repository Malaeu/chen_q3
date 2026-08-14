# Goal 058 G3 — mode-four physical scale closeout

Date: 2026-08-14

```text
VERDICT: G3_MODE4_PHYSICAL_SCALE_PROVED
STOP: MODE4_PHYSICAL_SCALE_PROVED_SOURCE_PSI4_CROSSWALK_MODE0_FOURIER_AND_LEMMA72_MISSING
SCOPE: ABSTRACT_SOURCE_FAMILY / LEAN
G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
```

## Exact result

The production file

```text
q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersPhysicalProlateScaling.lean
```

defines the exact physical-window series and proves:

```lean
Mode4FerrersRegularEvenProlateSolution.physical_contDiffOn_two_open
Mode4FerrersRegularEvenProlateSolution.physicalFerrersSeries_hasDerivAt_firstDerivativeSeries
Mode4FerrersRegularEvenProlateSolution.physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries
Mode4FerrersRegularEvenProlateSolution.physicalProlateDifferentialEquation
exists_mode4MatchedNormalizedPhysicalProlateRow_of_root
```

The scale is literally

```text
x = u / sqrt(mProject)
lambda = sqrt(mProject)
c = 2*pi*mProject = 2*pi*lambda^2
mode4JacobiG mProject = c^2.
```

On `(-sqrt(mProject),sqrt(mProject))`, the scaled series is `C2`, its two
declared scaled derivative series are actual derivatives, and it satisfies

```text
-(m-u^2) h''(u) + 2u h'(u) + (2*pi*sqrt(m)*u)^2 h(u)
  = (Lambda + mode4JacobiG m) h(u).
```

The final theorem packages those conclusions for the already existing
root-conditioned normalized row.  No source-mode predicate or new spectral
hypothesis is introduced.

## Knowledge preflight

The resolved card

```text
ACTIVE/pipeline/oracle_questions/2026_08_14_goal058_g3_mode4physicalscale_mode_four_ferrers_sqrt_m_sqrt_m_pw_lambda_ode.md
```

records three sequential `q3_docs` queries.  They found the source-pinned
architecture memorandum and current dimensionless solution, but no existing
Lean physical-scale supplier.  The leaf was therefore implemented locally;
no external review or Aristotle request was needed.

## Validation

```text
lake env lean Q3/Proofs/RouteB/D0Mode4FerrersPhysicalProlateScaling.lean  PASS
lake build Q3.Proofs.RouteB.D0Mode4FerrersPhysicalProlateScaling          PASS (7771 jobs)
lake build                                                               PASS (7817 jobs)
bash ../scripts/q3_check.sh Q3/Proofs/RouteB/D0Mode4FerrersPhysicalProlateScaling.lean
                                                                           PASS
forbidden-token scan                                                      PASS (zero hits)
forbidden-claim scan                                                      PASS (zero hits)
git diff --check                                                          PASS
```

Every public declaration has axiom surface exactly

```text
[propext, Classical.choice, Quot.sound]
```

The source file is `10245` bytes, `228` newline-terminated lines, has a final
LF, and SHA-256
`867236c5ca9844d822f8084a0dfa3a7159b96cf8c015a5ae1499fe9a8cfe8c06`.

The `UnicodeBasic` dependency emitted its pre-existing local-changes warning;
it did not change any exit code or axiom surface.

## What moved

The physical scale and derivative-chain wall is closed.  The next exact G3
source theorem is no longer another ODE calculation.  It is the Route-C
coefficient/minimal-tail crosswalk:

```text
classical regular degree-four psi4 Legendre coefficients
  -> current exact recurrence
  -> current minimal right-tail branch
  -> mode4RootFunction mProject (4*mProject) Lambda = 0
  -> normalization uniqueness and ordered psi4 identification.
```

The analogous mode-zero source package is still absent.

## Nonclaims

- `NO_MATCHING_ROOT_EXISTENCE`
- `NO_ORDERED_PSI4_IDENTIFICATION`
- `NO_MODE_ZERO_CONSTRUCTOR`
- `NO_FINITE_FOURIER_EIGENRELATION`
- `NO_PRODUCTION_PROLATEPAIR_CONSTRUCTION`
- `NO_LEMMA_7_2_RATE`
- `NO_DENOMINATOR_FLOOR`
- `NO_G3`
- `NO_G1`
- `NO_ROUTE_B_PROMOTION`
- `NO_RH`
