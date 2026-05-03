# Step 27 -- Directed finite certificate family skeleton

## Goal

Create a theorem-facing interface above accepted `FinitePenaltyCert` rows.

Step 26 gives:

\[
\texttt{PASS manifest row}
\Rightarrow
\texttt{FinitePenaltyCert}
\Rightarrow
\text{finite boundary-null positivity}.
\]

Step 27 adds the next shell:

\[
\texttt{FinitePenaltyCert}
\Rightarrow
\texttt{CertifiedFiniteBlock}
\Rightarrow
\texttt{DirectedCertFamily}.
\]

This is a skeleton only.  It does not prove analytic exhaustion.

## New Lean file

```text
Q3/Proofs/PSD_CertificateFamily.lean
```

New objects:

- `FiniteSpaceLabel`
- `CertifiedFiniteBlock`
- `HasRefinement`
- `DirectedCertFamily`
- `BoundaryNullExhaustive`
- `BoundaryNullGlobalPositivity`
- `DirectedFamilyClosure`

Consumer:

```text
boundaryNull_global_positivity_statement_of_closure
```

There are no new axioms and no `sorry`s.

## Generated seed

```text
docs/insights/q3_psdpd_directed_family_seed.json
```

Current accepted blocks:

| role | block_id | L | k | ell | delta | theta |
|---|---|---:|---:|---:|---:|---:|
| primary | `psdpd_L3_k11_ell030_delta025_theta1e4` | 3.0 | 11 | 0.30 | 0.25 | `1e-4` |
| control | `psdpd_L3_k9_ell030_delta025_theta1e5` | 3.0 | 9 | 0.30 | 0.25 | `1e-5` |

The seed status is:

```text
seed_only_not_exhaustive
```

## Meaning

The directed-family seed records accepted finite certificate blocks and their
artifact hashes.  It also records conservative rational floors for the safe
lower bounds.

It does not yet assert a refinement relation between the current blocks.  The
`known_refinements` list is intentionally empty.

## Remaining theorem targets

1. Define the directed refinement relation.
2. Prove the boundary-null correction lemma.
3. Prove density/exhaustion of the finite spaces.
4. Prove continuity of the Weil/PSD form in the chosen topology.
5. Produce a uniform certificate family, not just isolated finite blocks.

## Verdict

Step 27 creates the formal consumer interface:
`FinitePenaltyCert` rows can now sit inside a directed-family shell.

The next real theorem is boundary-null exhaustion.
