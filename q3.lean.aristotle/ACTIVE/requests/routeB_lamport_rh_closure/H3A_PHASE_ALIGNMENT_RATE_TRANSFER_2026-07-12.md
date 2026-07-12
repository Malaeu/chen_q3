# Route B H3a phase-alignment rate transfer — revision 27

Status: `H3A1_PROVED / EXACT_GROUND_TRIAL_PROJECTIVE_RATE_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS`

This transaction proves the generic complex-Hilbert phase alignment and the
transfer from projective defect to phase-aligned norm error.  It does not
select the exact Route B ground vector or trial vector, prove the projective
defect rate, choose the same family/filter as H3b, close H3a/H3, create Bus
010, or prove RH.

## 1. Total canonical phase

For a complex scalar `z`, define

```text
alignmentPhase(z) = 1                    if z=0,
alignmentPhase(z) = z / ||z||            otherwise.
```

Lean proves for every `z`:

```text
||alignmentPhase(z)|| = 1,
conj(alignmentPhase(z)) * z = ||z||.
```

The definition is total, so the generic algebra never divides by zero.

## 2. Exact unit-vector identity

For unit vectors `u,v` in any complex inner-product space, expanding the norm
and using the canonical phase gives

```text
||alignmentPhase(<u,v>) u - v||^2
  = 2 - 2 ||<u,v>||.
```

This is theorem

```text
phase_alignment_norm_sq.
```

Cauchy--Schwarz gives `0<=||<u,v>||<=1`, hence

```text
1-||<u,v>|| <= 1-||<u,v>||^2
```

and the quantitative bound

```text
||alignmentPhase(<u,v>) u-v||
  <= sqrt(2*(1-||<u,v>||^2)).
```

## 3. Filter-level rate transfer

On a non-bottom filter, if `u_i` and `v_i` are eventually unit and

```text
1-||<u_i,v_i>||^2 -> 0,
```

then Lean proves

```text
||alignmentPhase(<u_i,v_i>) u_i-v_i|| -> 0.
```

Verdict:

```text
GENERIC_PHASE_ALIGNMENT_RATE_TRANSFER_LEAN.
```

## 4. Exact Route B obligation left open

The source itself labels the approximation of the prolate trial to a scalar
multiple of the minimal eigenvector as a main remaining obstacle.  H3a2 must
still provide:

1. the exact same H1c3/D0.8 ground-vector family;
2. a legal simple-even normalized ground selector;
3. the exact normalized trial on a cofinal nonzero locus;
4. the source-locked estimate
   `1-||<ground_i,trial_i>||^2 -> 0` at the weighted rate needed by H3b;
5. one shared non-bottom family/filter for H3a, H3b, H3c, and H3e;
6. a Lean export connecting the exact objects to this generic theorem.

The exact stop is

```text
H3A_EXACT_PROJECTIVE_RATE_INSTANTIATION_MISSING.
```

D0.5 supplies types, a set-valued ground space, conditional trial
normalization, and a Rayleigh inequality.  It explicitly does not supply a
simple-even selector or a ground/trial rate.

## 5. Honest DAG split

```text
H3a GroundTrialTracking                         OPEN / AND
|-- H3a.0 H3aDecompositionContract              PROVED
|-- H3a1 GenericComplexPhaseAlignmentCore       PROVED / LEAN
|-- H3a2 ExactGroundTrialProjectiveRate          OPEN / INELIGIBLE
`-- H3a3 H3aAssembly                            OPEN / INELIGIBLE
```

The generic uncertainty `PHASE_ALIGNMENT_MISSING` is retired.  The exact
source-level stop `GROUND_TRIAL_TRACKING_MISSING` remains.

## 6. Mathlib source boundary

Official inner-product API:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html

Mathlib certifies complex inner-product and norm geometry.  It does not supply
the Route B ground/trial objects or their projective-defect rate.

## 7. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/PhaseAlignmentRateTransfer.lean
```

It compiles without `sorry`, `admit`, or `exact?`; printed axiom sets contain
only

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_EXACT_GROUND_VECTOR_SELECTION
NO_SIMPLE_EVEN_GROUND
NO_COFINAL_TRIAL_NONZERO
NO_EXACT_PROJECTIVE_DEFECT_RATE
NO_SAME_FAMILY_FILTER_SELECTION
NO_H3A_PARENT_CLOSURE
NO_H3_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
