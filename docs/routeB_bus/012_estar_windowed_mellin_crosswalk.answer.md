# 012 — EStarWindowedMellinCrosswalk

Date: `2026-07-27`

```text
ESTAR_CONTINUATION_LEMMA_MISSING
missing lemma: EStarMuntzZeroMassContinuation
```

## Lean artifact

```text
Q3/Proofs/RouteB/EStarWindowedMellinCrosswalk.lean
720 lines
```

The source function remains parametric:

```lean
h : ℝ → ℂ
hmass : ZeroPositiveMass h
```

No concrete `hTrial_m` is selected in the file.

## T1 — exact finite-window identity

Main declarations:

```lean
WindowFiniteSupport
dirichletWindow
dirichletWindow_eq_constraint_sum
windowedMellin_E_star_eq_weightedDirichletWindowIntegral
```

The proved kernel is

\[
D_{\lambda,p}(v)
=\sum_{n\in S}
  \mathbf 1_{\{v/\lambda\le n\le v\lambda\}}\,n^{-p}.
\]

The proved identity is

\[
\mathcal M\!\left(
  1_{[\lambda^{-1},\lambda]}\mathcal E_*h
\right)(s)
=
\int_0^\infty
  v^{s-\frac12}h(v)D_{\lambda,s+\frac12}(v)\,dv.
\]

The only comb used under the integral is the finite `Finset S`.  The bridge
back to the D0 `E_star` is the explicit `WindowFiniteSupport` certificate.
There is no infinite sum/integral exchange in T1.

## T2 — zero-mass decomposition in the absolute domain

Main declarations:

```lean
ZeroPositiveMass
EStarMellinAbsolute
lowerMellinTail
upperMellinTail
mellin_E_star_eq_riemannZeta_mul
windowedMellin_E_star_zeroMass_decomposition_abs
```

Under

```lean
hmass : ZeroPositiveMass h
hp    : 1 < (s + 1 / 2).re
habs  : EStarMellinAbsolute h (s + 1 / 2)
hEconv : MellinConvergent (E_star h) s
1 ≤ lambda
```

Lean proves

\[
\mathcal M\!\left(
  1_{[\lambda^{-1},\lambda]}\mathcal E_*h
\right)(s)
=
\zeta\!\left(s+\tfrac12\right)
  \mathcal M(h)\!\left(s+\tfrac12\right)
-R^-_\lambda(s)-R^+_\lambda(s),
\]

with exact definitions

\[
R^-_\lambda(s)=
\mathcal M(1_{(-\infty,\lambda^{-1})}\mathcal E_*h)(s),
\qquad
R^+_\lambda(s)=
\mathcal M(1_{(\lambda,\infty)}\mathcal E_*h)(s).
\]

No bound or smallness claim is made for either tail.

### Post-audit scope note

In the absolute-domain theorem, `hmass` is deliberately present but
definitionally unused: the proof locks and clears it.  Zero mass is required
for the continuation into the strip, not for the absolute-domain algebra.
Thus `zeroMass_decomposition_abs` is a stronger name than the minimal
absolute-domain contract.

The local Q3 semantic search and the Mathlib source scan found the scaling,
Mellin-holomorphy, and zeta Dirichlet-series ingredients, but no theorem that
continues this zero-mass identity from the absolute domain to
`|Re s| < 1/2`.  That continuation is isolated as the missing lemma named in
the status block; it is not represented by an axiom or a hole.

## Mandatory nonzero-mass pole plant

```lean
nonzeroMassPlant v = 1_(0,1](v)
```

Lean proves:

```text
nonzeroMassPlant ≥ 0
integral_(0,∞) nonzeroMassPlant = 1
not ZeroPositiveMass(nonzeroMassPlant)
```

For

\[
J_\lambda(t)=
\frac{\lambda^{1/2-t}-\lambda^{t-1/2}}{1/2-t},
\]

Lean proves the exact pole-window ratio

\[
\frac{J_\lambda(-\sigma)}{J_\lambda(0)}
=
\frac{\lambda^\sigma}{1+2\sigma}
\cdot
\frac{1-\lambda^{-1-2\sigma}}{1-\lambda^{-1}}
\ge
\frac{\lambda^\sigma}{1+2\sigma}
\qquad(\lambda>1,\ \sigma\ge0).
\]

Thus the mass-one plant retains the registered `lambda^sigma` pole growth.
A bounded implementation would not satisfy these proved identities.

This indicator is a pole-counterterm plant, not a plant in the T2 Lipschitz
regularity class.  The triangular Lipschitz PL2 is not discharged by 012 and
remains an explicit obligation of the repaired v2 continuation contract.

The standalone continuation contract v1 is separately archived
`FATAL / DO_NOT_EXECUTE` under `ZETA_RAW_POLE_VALUE_MISMATCH`; this does not
invalidate the absolute-domain identities proved in 012.

## Validation

```text
lake env lean Q3/Proofs/RouteB/EStarWindowedMellinCrosswalk.lean
exit: 0

lake build
exit: 0
Build completed successfully (7817 jobs).

#print axioms declarations checked: 29
each result: [propext, Classical.choice, Quot.sound]
sorryAx: 0

grep sorry/admit/exact?/native_decide/@[implemented_by]/axiom
matches in new Lean file: 0
```

## Source locks

```text
9b8bb057708b1d04a21c27c1aebaf10fdeb6d7fd5851ee5f3638d33ce2f63e05
  Q3/Proofs/RouteB/EStarWindowedMellinCrosswalk.lean

a322424d51aad88d4ee2d366220ad6ea2c4cea02c96bc07a6d97f247203b7a97
  012_estar_windowed_mellin_crosswalk.goal.md

ed2217c1b65cf640b388fc26586f9eeb56340fcee8b7e06402c88f053381b3fa
  proshka/PROSHKA_MELLIN_CROSSWALK_2026-07-27.md

aabaf47cb484f0157fd7b2ac4f30811aec9595116c1193715e41de8b520393cd
  Q3/Proofs/RouteB/D0KTrialStage2.lean
```

## State

```text
ROUTE_B_STATE.md: untouched
ROUTE_B_EXECUTION_STATE.json: untouched
Bus 010: not created
Project status: CHALLENGER / NOT_RH
```
