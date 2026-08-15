# Goal 058 G3 — selected mode-zero/mode-four Ferrers/physical closeout

Date: 2026-08-15

Verdict:

```text
MODE_ZERO_FOUR_SELECTED_FERRERS_PHYSICAL_PASS
G1_STATUS: OPEN
G3_STATUS: OPEN
ROUTE: CHALLENGER_NOT_RH
STOP_CODE: G3_SELECTED_MODE_ZERO_FOUR_REGULAR_PHYSICAL_SOLUTIONS_PROVED_ENDPOINT_GREEN_FOURIER_ZERO_COUNTS_AND_LEMMA72_NEXT
```

## Exact result

The new public theorem

```text
exists_modeZero_modeFour_selectedFerrersRegularEvenProlateSolutions
```

constructs both existing regular source objects at the exact zero-based even
carrier indices `0` and `2` and proves

```text
Lambda_0 < Lambda_2 < 20.
```

Each witness is a `Mode4FerrersRegularEvenProlateSolution`, so it carries the
normalized DLMF left row, absolute and square summability, exact recurrence,
closed-window continuity, interior `C2`, exact prolate ODE, and both zero-flux
endpoint conditions.  The already imported physical-scaling theorems apply to
each witness on `(-sqrt(mProject), sqrt(mProject))`.

The proof adds no source assumption.  It derives the exact matching roots from
the strict finite-limit carrier theorem and the literal Schur determinant/root
identity, then invokes the existing root-conditioned constructor twice.

## Search and validation receipt

The fresh declared EnvDump completed with 256/256 current source-backed Route B
modules, 2334 declarations, no stale or uncovered module, and no proof hole or
nonstandard axiom.  Six source-less orphan oleans were excluded.

The exact supplier query

```text
mode zero degree four selected classical even carrier indices zero two Ferrers
regular physical prolate solutions strict eigenvalue order below twenty
```

returned `CANDIDATE_ONLY`: the carrier and root-conditioned Ferrers theorems
were neighboring suppliers, not the paired composition.

Validation:

- direct `lake env lean`: PASS;
- named target build: PASS, 7794 jobs;
- `scripts/q3_check.sh`: PASS;
- `git diff --check`: PASS;
- public axiom surface: exactly
  `[propext, Classical.choice, Quot.sound]`.

The first `q3_check` run correctly rejected the literal forbidden marker name
inside the module's search-receipt prose.  The proof was already green; the
receipt wording was repaired and the checker then passed.  This is another
healthy self-hit by the same fail-closed system that writes the artifacts.

## Boundary and next seam

This theorem does not create or replace `ProlatePair`.  It does not yet prove
the exact interior zero counts `0/4`, the restricted finite-Fourier
eigenrelations, positivity/order of Fourier eigenvalues, orthogonality, CCM
Lemma 7.2, the central-overlap/denominator floor, the coupled schedule, G1,
G3, Route B promotion, or RH.

The next analytic seam is the Green/intertwining theorem for the actual
endpoint interface: interior `C2` plus the proved zero-flux limits.  The older
commutation theorem requires a globally `C2` test function and therefore
cannot be applied by pretending the compact-window Ferrers modes have a
stronger endpoint domain.

