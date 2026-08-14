# Goal 058 G3 - classical spectrum to literal Schur inertia source packet

Date: 2026-08-14

Status: `SOURCE_PACKET_COMPLETE_REVIEW_FORK_OPEN`

Boundary: read-only source acquisition and theorem-contract synthesis. No
production Lean theorem, endpoint count, matching root, G3 closure, Route B
promotion, or RH claim is asserted here.

## Exact current consumer

The unchanged production consumer is

```lean
exists_mode4RootFunction_eq_zero_of_hermitianSchur_counts_two_three
```

in `Q3/Proofs/RouteB/D0Mode4SchurHermitianSymmetrization.lean`.  For the
literal matrix

```lean
mode4HermitianSchurMatrix mProject Lambda K
```

it requires two nonsingular endpoints, `LambdaLower <= LambdaUpper <= 20`,
and negative counts `2` and `3`.  The canonical split is `K = 4*mProject`.
The exact infinite recessive-tail correction is part of this matrix and may
not be replaced by a plain finite truncation.

## Current-tree facts already proved

The following are kernel checked and axiom-clean up to the standard
`[propext, Classical.choice, Quot.sound]` surface.

1. `mode4JacobiCoefficients_eq_pswfLegendre_evenCrosswalk` identifies the
   literal project recurrence with DLMF 30.8.3--30.8.4 after
   `G = mode4JacobiG mProject` and spectral energy `E = Lambda + G`.
2. `mode4BackwardTail_tendsto_rightTailLimit` constructs the exact right-tail
   ratio as the terminal-independent limit of finite backward tails.
3. `mode4HermitianTail_boundaryFlux_eq_schurCorrection` identifies that ratio
   with the newest diagonal correction in the literal Hermitian Schur matrix.
4. `mode4DLMF3084_3085_degreeFour_coefficients_force_root` proves that a
   supplied reindexed degree-four/order-zero DLMF row satisfying the literal
   recurrence and raw `1/9` normalization forces the current
   `mode4RootFunction = 0`.
5. The spectral-parameter strict drop, simple root kernel, one-direction
   inertia jump, and injective root-inertia label are already proved.  They
   label supplied roots but do not construct the classical indexed root.

## Previously pinned primary sources rechecked

- Osipov, TR-1450, physical pages 4--5, Theorems 1 and 3:
  `psi_n` is real, orthonormal, parity indexed, has exactly `n` simple
  interior zeros, and the regular closed-window differential spectrum is a
  strictly increasing sequence `chi_0 < chi_1 < ...`; every regular solution
  at `chi_n` is a multiple of `psi_n`.
- Bonami--Karoui, arXiv:1405.3676v2, physical pages 1, 3, and 5:
  the positive prolate Sturm--Liouville operator, parity convention, classical
  bounds, and indexed zero count agree with the project crosswalk.  In
  particular `chi_4 - c^2 <= 20`.
- Slepian--Pollak, BSTJ 40 (1961), printed pages 57--58 and 62:
  the regular indexed angular prolate functions satisfy the finite-Fourier
  eigenrelation and form the complete indexed family.

The rendered pages were inspected again in this run.  These sources establish
the classical spectrum and its index, but none of the three papers states the
negative count of the project's exact-tail Schur matrix.

## New primary-source discriminator: DLMF finite-matrix limits

NIST DLMF version 1.2.7, release date 2026-06-15, was checked at the official
permalinks on 2026-08-14.

### DLMF 30.8

- 30.8.1--30.8.2 define the Ferrers expansion and its coefficients by the
  exact Legendre pairing.
- 30.8.3--30.8.4 give the three-term recurrence.
- 30.8.5 gives its normalization.
- 30.8.7 identifies the coefficient row as the recessive branch at infinity.

Official equation endpoints used here:

```text
https://dlmf.nist.gov/30.8.E1.tex
https://dlmf.nist.gov/30.8.E2.tex
https://dlmf.nist.gov/30.8.E3a.tex
https://dlmf.nist.gov/30.8.E3b.tex
https://dlmf.nist.gov/30.8.E3c.tex
https://dlmf.nist.gov/30.8.E4.tex
https://dlmf.nist.gov/30.8.E5.tex
https://dlmf.nist.gov/30.8.E7.tex
```

### DLMF 30.16

For the even sector, 30.16.1 defines a finite tridiagonal matrix.  Its entries
are exactly the DLMF 30.8 recurrence coefficients with even degree beginning
at zero.  If its ordered eigenvalues are `alpha_(j,d)`, then

```text
alpha_(j,d+1) <= alpha_(j,d),                         (30.16.2)
lambda_n^m(gamma^2) = lim_(d->infinity) alpha_(p,d), (30.16.3)
p = floor((n-m)/2) + 1.
```

For `m=0,n=4`, the selected position is literally `p=3`; for `m=0,n=0`, it
is `p=1`.  Equations 30.16.7--30.16.9 additionally normalize the finite
eigenvectors and identify their limits with the DLMF coefficient row and the
indexed spheroidal function itself.

Exact official TeX SHA-256 pins:

```text
5ded12f503ce3a658a73687976926264d51aae185838993f0bc27b9cd1326f22  30.16.E1a.tex
146c9d584200e12850b5bfa7cb2fea7b2e515aa63993080730da31070141506a  30.16.E1b.tex
d194f48cbc8f81930dbf9546864a5e2041307f21024093a33a7091d40feffb5e  30.16.E1c.tex
c0e5f1b968b4bcb1b61a6d72dcb739f6b8228c3934987b992595bc4168854cbd  30.16.E2.tex
35b0b61b184dd56ecd3b17a20de6f9e13f00533b56fbfa0b4a6e544820629e4d  30.16.E3.tex
76e0d10814b5793154042604984c77f26c1b94408ec299290154b71c0f6d9524  30.16.E4.tex
c0f3812292eb10516d92e9d2dcfa9ff162df7a87acb9fd9f84249de01f25e1a5  30.16.E7.tex
9457aa9ba839c63ba3bd4dfbd370947e79b83a14e7ef0172d28f88ee60a4b05c  30.16.E8.tex
87b58c2c8add1d9b80681f6447f605d27b5f1dda1467f35172491c289dcfe383  30.16.E9.tex
```

The DLMF evidence is stronger than the previously pinned recurrence-only
crosswalk: it exposes both the ordered finite spectral approximants and the
literal `p=3` coefficient/function limit.

## Exact finite-dimensional route to the Schur count

The source packet reveals a route that does not require formalizing an
unbounded infinite Jacobi operator.

Let `J_d(Lambda)` be the finite `d x d` even DLMF Jacobi matrix after the
existing Hermitian diagonal similarity and the shift by `Lambda + G`.  Split
it at `K` into the first `K` coordinates and the finite tail.

1. The current tail-separation inequality for `q >= K`, together with
   `Lambda <= 20`, should prove the finite tail block positive definite.
2. Finite block Gaussian congruence then gives exact inertia additivity:

   ```text
   negCount(J_d(Lambda)) = negCount(S_(K,d)(Lambda)).
   ```

   There is no tail contribution because the eliminated tail is positive.
3. `S_(K,d)` differs from the current literal Schur matrix in only the newest
   diagonal.  Its scalar correction is the finite backward tail and therefore
   converges to `mode4RightTailLimit` by an already proved theorem.
4. At a nonsingular endpoint, finite-dimensional eigenvalue continuity makes
   the negative count eventually equal to the negative count of the literal
   limit Schur matrix.
5. DLMF 30.16.2--30.16.4 make the negative count of `J_d` eventually equal to
   the number of classical even eigenvalues below `Lambda + G`.

Consequently the exact target is

```text
negativeCount(mode4HermitianSchurMatrix mProject Lambda K)
  = #{r | chi_(2*r)(sqrt G) - G < Lambda}.
```

The finite-split offset is predicted to be exactly zero, for three explicit
reasons that must each be proved:

- the finite matrix starts with even Legendre degree zero (`q=0`), so no left
  classical mode is omitted;
- reversal and positive diagonal symmetrization preserve inertia;
- the eliminated `q >= K` tail is positive and hence contributes zero negative
  directions.

This is an exact theorem plan, not yet a theorem.  Silently writing offset
zero before those congruence and positivity proofs would still be invalid.

## Required Lean leaf decomposition

The crosswalk can be kept finite-dimensional if it is decomposed as follows.

1. `mode4DLMFEvenFiniteMatrix_similar_hermitianLeftContinuantMatrix`:
   exact index, shift, reversal, and positive diagonal similarity.
2. `mode4FiniteJacobiTail_posDef` for `Lambda <= 20`, `q >= K`, under the
   current production separation inequality.
3. `mode4FiniteJacobi_negativeCount_eq_finiteSchur_negativeCount`:
   explicit finite block congruence / inertia additivity.
4. `mode4FiniteSchur_tendsto_hermitianSchurMatrix`:
   the already constructed backward-tail convergence lifted to the one
   changing diagonal matrix entry.
5. `mode4HermitianNegativeCount_eventually_eq_of_tendsto_det_ne`:
   local constancy of finite Hermitian inertia away from determinant zero.
6. `mode4DLMFEvenFiniteMatrix_negativeCount_eventually_eq_classicalCount`:
   the exact use of DLMF 30.16 ordered eigenvalue convergence at a separator.
7. The production composition, with the offset proved to be zero, followed by
   Bonami--Karoui separators to discharge counts `2` and `3`.

No leaf above is an Aristotle task yet: the source semantics and the preferred
route must first be judged.

## Competing smaller route exposed by the same source

DLMF 30.16.7--30.16.9 also opens a direct indexed-row route.  For
`m=0,n=4,p=3`, the limiting finite eigenvector is the exact coefficient row
and its Ferrers series is the indexed `psi_4`.  The current theorem
`mode4DLMF3084_3085_degreeFour_coefficients_force_root` then forces the literal
matching root without first proving a global Schur-count identity.

This route is potentially smaller for root existence, and `p=1` supplies the
mode-zero companion.  It must include the DLMF function identity, not merely a
row satisfying recurrence and normalization; otherwise it would not source
the finite-Fourier eigenrelation required by `IsActualProlateModePair`.

## Review fork

Mythos and Proshka must choose between:

- `ROUTE_INERTIA_FINITE_LIMIT`: prove the seven finite-dimensional leaves and
  obtain endpoint counts `2/3` with exact offset zero; or
- `ROUTE_DLMF_INDEXED_ROW_LIMIT`: formalize the `p=3` and `p=1` DLMF
  eigenvector/function limits and feed the existing exact root/function
  consumers directly.

The review must reject any answer that replaces the exact-tail Schur matrix,
assumes the indexed row, assumes offset zero, or calls a finite numerical
truncation a source theorem.

## Nonclaims

- `NO_CLASSICAL_TO_SCHUR_INERTIA_THEOREM_YET`
- `NO_PROVED_OFFSET_YET`
- `NO_INDEXED_DLMF_ROW_CONSTRUCTOR_YET`
- `NO_ENDPOINT_COUNTS_YET`
- `NO_MATCHING_ROOT_EXISTENCE_YET`
- `NO_ACTUAL_PROLATE_PAIR_EXISTENCE_YET`
- `NO_LEMMA72_RATE_OR_DENOMINATOR_FLOOR`
- `NO_G3`
- `NO_G1`
- `NO_ROUTE_B_PROMOTION`
- `NO_RH`
