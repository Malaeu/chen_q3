# Goal 058 G3 — exact PSWF index and Fourier source-pin packet

Date: 2026-08-14

Status: PRIMARY SOURCES PINNED; LEAN SELECTION/CONSTRUCTOR STILL OPEN

## Purpose

This packet closes the bibliographic uncertainty behind the current
`G3_MODE4_FOUR_INTERIOR_ZEROS_AND_THIRD_EVEN_SELECTION` source wall.  It does
not assert a new Lean theorem.  It records exact on-disk primary-source pages,
the project-variable crosswalk, and the remaining formal transport.

## Locked local sources

1. Andrei Osipov, *Explicit upper bounds on the eigenvalues associated with
   prolate spheroidal wave functions*, Yale Research Report
   `YALEU/DCS/TR-1450` (2012):

   - local file: `docs/routeB_bus/litreview/pdfs/TR1450.pdf`;
   - SHA-256:
     `98f4aa8448d8b09fe5982361d2c489bfb41e592acc6695251c9939bd7a4fce57`;
   - physical PDF page 4, Theorem 1;
   - physical PDF page 5, Theorem 3.

2. Aline Bonami and Abderrazek Karoui, *Uniform approximation and explicit
   estimates for the prolate spheroidal wave functions*, arXiv:1405.3676v2:

   - local file: `docs/routeB_bus/litreview/pdfs/1405.3676.pdf`;
   - SHA-256:
     `9fe8dc39e4440200a29ff94bb640b693c06a176d28b7e38a468dce98afa7d7b8`;
   - physical PDF page 1, equations (1)--(2);
   - physical PDF page 3, equations (4)--(5) and the parity convention;
   - physical PDF page 5, explicit use of exactly `n` interior zeros and
     Sturm comparison.

3. Victor Katsnelson, *Self-adjoint boundary conditions for the prolate
   spheroid differential operator*, arXiv:1603.07542v1:

   - versioned project lock:
     `D0_3F_EXTERNAL_SOURCE_LOCK.json`;
   - lock SHA-256:
     `6822e3e5b254bb0280262020ab2cd2d3bcc57b1f0453b560144a13bbae2b7919`;
   - exact source labels: `MaxDO/maxdo1`, `FBC`, `DiSp`, `DSOIT`,
     `WECF/DDLI`.

All five rendered pages used here were visually inspected after Poppler
rendering.  The displayed formulae, theorem numbers, page numbers, and text
match the extracted text.

## Exact source content

### TR-1450, page 4, Theorem 1

For `c > 0`, with

```text
F_c phi (x) = integral_{-1}^{1} phi(t) exp(i c x t) dt,
```

the indexed eigenfunctions `psi_n` are real, orthonormal, and complete in
`L2[-1,1]`.  Even indices give even functions and odd indices give odd
functions.  `psi_n` has exactly `n` simple roots in `(-1,1)`.  Every
finite-Fourier eigenvalue is nonzero and simple, with phase
`lambda_n = i^n |lambda_n|`.

The same page records equations (5)--(10), including the finite-Fourier
eigenrelation and

```text
Q_c = (c / (2*pi)) F_c^* F_c,
mu_n = (c / (2*pi)) |lambda_n|^2.
```

Consequences fixed by the source indexing:

- `psi_0`: even, zero interior roots, positive real Fourier phase;
- `psi_4`: even, exactly four simple interior roots, positive real Fourier
  phase because `i^4 = 1`;
- `psi_4` is the third even mode (`psi_0`, `psi_2`, `psi_4`), not the second
  even mode.

Because the source orders the finite-Fourier eigenvalues by decreasing
absolute value and both indices 0 and 4 have positive real phase, simplicity
gives the strict source ordering needed by the production names
`chi2 < chi0` after the index crosswalk.

### TR-1450, page 5, Theorem 3

For every `c > 0`, there is a strictly increasing unbounded positive sequence
`chi_0 < chi_1 < ...`.  At `chi_n`, the equation

```text
(1 - x^2) psi'' - 2*x*psi' + (chi_n - c^2*x^2)*psi = 0
```

has a solution continuous on `[-1,1]`, and every such solution is a constant
multiple of the finite-Fourier eigenfunction `psi_n`.

This is the exact source bridge from the regular closed-window ODE solution to
the indexed finite-Fourier mode.  It is not merely a statement that the two
operators commute.

### Bonami--Karoui independent cross-check

Physical page 1 defines the same positive-phase `F_c`, its band-limiting
operator `Q_c`, and the Sturm--Liouville expression

```text
L_c psi = -d/dx ((1 - x^2) psi') + c^2*x^2*psi.
```

Physical page 3 uses the closed-window smooth solution, its parity matching
the index, and the same differential equation.  Physical page 5 explicitly
uses the fact that `psi_n` has exactly `n` zeros in `(-1,1)` inside a Sturm
comparison argument.  This independently confirms the index convention used
by TR-1450.

## Exact project crosswalk

For
`S : Mode4FerrersRegularEvenProlateSolution mProject K Lambda`, the stored
equation is

```text
-(1-x^2) S'' + 2*x*S' + G*x^2*S = (Lambda + G)*S,
G = mode4JacobiG mProject.
```

Therefore the dimensionless primary-source variables are

```text
c^2   = mode4JacobiG mProject,
chi_n = Lambda + mode4JacobiG mProject.
```

The existing constructor already supplies:

- `G > 0` for the live `mProject` range;
- a nonzero normalized real coefficient row;
- an even function continuous on `[-1,1]`;
- actual first and second derivatives on `(-1,1)`;
- the exact ODE above;
- both natural zero-flux endpoint limits.

The Katsnelson source lock identifies those zero-flux conditions with the
canonical self-adjoint realization.  Thus the endpoint convention is no
longer bibliographically ambiguous.

For the physical production window, the already locked scaling is

```text
c = 2*pi*lambda^2,
y = x/lambda,
```

with positive kernel phase.  This scale/phase transport remains a separate
Lean bridge and must not be inferred merely from the dimensionless theorem.

## What this packet resolves

- exact source theorem for zero-count indexing: found and page-pinned;
- exact parity/index convention: found and page-pinned;
- exact ODE-to-finite-Fourier mode identification: found and page-pinned;
- finite-Fourier eigenvalue nonvanishing and phase at indices 0 and 4: found
  and page-pinned;
- canonical singular endpoint realization: already version-locked in the
  Katsnelson packet.

The primary sources jointly support the intended source statement; no new
analytic hypothesis needs to be invented for the target semantics.

## Remaining Lean wall

The current mode-four constructor is conditional on

```text
mode4RootFunction mProject K Lambda = 0.
```

It does not yet prove that `Lambda + G` is the source eigenvalue `chi_4`, nor
that the constructed solution has exactly four interior zeros.  The bounded
nodal-interval comparison theorem prepared for Aristotle is only the first
kernel toward that selection.  After it, the formal route still needs:

1. compact-interior zero finiteness and consecutive nodal-pair extraction;
2. a source-faithful ordering/oscillation ladder locating the matching root at
   index 4;
3. the analogous index-0 constructor;
4. the dimensionless-to-physical scale and normalization bridge;
5. assembly of the production `ProlatePair` satisfying
   `IsActualProlateModePair`;
6. the separate CCM Lemma 7.2 uniform rate and denominator-floor transport.

Theorem 1 supplies the restricted finite-Fourier eigenrelation only after the
current Ferrers solution is identified with `psi_4` (and the mode-zero
companion with `psi_0`).  It does not let the project skip the selection
proof.

## Nonclaims

- `NO_LEAN_OSCILLATION_INDEX_THEOREM_YET`
- `NO_MATCHING_ROOT_INDEX_IDENTIFICATION`
- `NO_MODE_ZERO_CONSTRUCTOR`
- `NO_PHYSICAL_SCALE_BRIDGE`
- `NO_PRODUCTION_PROLATEPAIR_CONSTRUCTION`
- `NO_LEMMA_7_2_RATE`
- `NO_DENOMINATOR_FLOOR`
- `NO_G3`
- `NO_G1`
- `NO_ROUTE_B_PROMOTION`
- `NO_RH`
