# 006 — D0 anchor floor

Date: `2026-07-27`

```text
ANCHOR_FLOOR_PROVED
```

## Source-lock precondition

| check | D0KTrialStage1–3 source | verdict |
|---|---|---|
| orthogonality in the normalization norm | `P_m_N=(E_m_N).orthogonalProjection` on `H_m`; `sTrial_m_N=‖gTrial_m_N‖⁻¹` | MATCH |
| `V₀` in `range P` | `0∈modeSet`; `E_m_N=span {V_n:n∈modeSet}`; materialized as `V0_mem_E_m_N` | MATCH |
| exact normalized trial | `kTrial_m_N=(‖P_m_N gTrial_m‖⁻¹:ℂ) • P_m_N gTrial_m` | MATCH |
| overlap phase/sign | no reality or sign theorem in Stage1–3; the theorem uses only the complex norm of the overlap | MATCH / NO PHASE INPUT |

No extra scalar or phase is present.  The abstract `CoefficientFamily` row is
connected to the constructed Stage-3 row by the exact equality `hbind`; it
contains no normalization freedom.

## Lean packet

File:

```text
Q3/Proofs/RouteB/D0AnchorFloor.lean
```

Declarations:

```text
V0_mem_E_m_N
inner_V0_gTrial_m_N_eq
norm_gTrial_m_N_le
gTrial_m_N_ne_zero_of_unprojected_central_mass
D0AnchorFloorFromUnprojectedCentralMass
```

The main theorem assumes

```text
a ≤ sqrt(L_m) * ‖<V₀,gTrial_m>‖
‖gTrial_m‖ ≤ C
0 < a
0 < C
```

and returns, for the exact Stage-3-bound coefficient row,

```text
P_m_N gTrial_m ≠ 0
∃ ci : CentralIndex D, ci.1 = i
a / C ≤ sqrt(L_m) * ‖D.kTrial i 0‖
a / C ≤ ‖rawFplus D i 0‖
```

## Six-line route

```text
V₀ ∈ E_m_N
→ <V₀,P_m_N gTrial_m> = <V₀,gTrial_m>
→ P_m_N gTrial_m ≠ 0
→ ‖c₀‖ = ‖<V₀,gTrial_m>‖ / ‖P_m_N gTrial_m‖
→ ‖P_m_N gTrial_m‖ ≤ ‖gTrial_m‖ ≤ C
→ ‖rawFplus(0)‖ = sqrt(L_m) ‖c₀‖ ≥ a/C.
```

No lower bound on `‖P_m_N gTrial_m‖`, weighted projection theorem,
phase-consistency assumption, RH input, numerical plateau, new axiom, `sorry`,
or `admit` is used.

## POSITIVITY diagnostic for the second lemma

The completed 4001-point probe remains diagnostic input for the future
`A_σ`/unprojected-moment lemma:

| `(m,N)` | min `Re q` | max `|Im q|` | fraction `Re q<0` | phase-aligned min/max |
|---|---:|---:|---:|---:|
| `(53,120)` | `-1.58502908854` | `1.96967794954e-16` | `0.892276930767` | `-2.44914694923e-9` |
| `(257,120)` | `-1.58096884549` | `2.01041602483e-16` | `0.853036740815` | `-9.57400729711e-9` |

The exact D0 phase has `c₀<0`; multiplying by `sign(c₀)=-1` gives the
phase-aligned column.  These numbers are not used by the anchor-floor proof.

## Validation

```text
lake env lean Q3/Proofs/RouteB/D0AnchorFloor.lean: exit 0
lake build: exit 0
sorry/admit in D0AnchorFloor.lean: 0

#print axioms D0AnchorFloorFromUnprojectedCentralMass
[propext, Classical.choice, Quot.sound]
```

Route B remains `CHALLENGER / NOT_RH`.  Bus 010 was not created.
