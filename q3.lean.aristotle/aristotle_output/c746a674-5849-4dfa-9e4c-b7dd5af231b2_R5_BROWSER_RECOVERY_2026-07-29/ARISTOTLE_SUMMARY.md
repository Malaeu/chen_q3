# Summary of changes for run 8b6a199c-da12-4497-86d9-d42914cccd87
MELLIN_DSLOPE_ANALYTICITY_GAP

Added `RequestProject/PoleSubtracted.lean`, containing a verified pole-subtracted framework:
- `MellinDivOne` with its value at `1`, off-pole quotient formulas, and analytic inheritance from an analytic/differentiable Mellin transform.
- `ZetaResidueFactor` with value `1` at the pole, the off-pole `(w-1) * riemannZeta w` formula, and a removable-singularity proof of analyticity.
- `ZetaMellinPoleSub`, including analyticity, off-pole equality with the ordinary zeta–Mellin product, and its derivative value at the pole.
- Generic identity-theorem continuation, punctured, and pole-value theorems, parameterized by the required analyticity of the Mellin and integral terms.
- Nonzero-pole-value and factor-removal plant theorems.

The remaining gap is deriving the concrete analyticity of `Mellin h`, `Gwin`, `Rminus`, and `Rplus` directly from the original support/Lipschitz hypotheses, together with the requested explicit triangular-bump plants. Thus the generic glue is proved, but the complete original contract is not.

Mathlib APIs used:
- Zeta pole: `riemannZeta_residue_one` and `differentiableAt_riemannZeta`.
- Removable singularity: `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`.
- Divided slope: `Complex.differentiableOn_dslope`.
- Identity theorem: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.

The project builds successfully. All new checked declarations use exactly `[propext, Classical.choice, Quot.sound]`, and touched Lean files contain no `sorry`, `admit`, `axiom`, or `native_decide`. `RESULT.md` contains exactly the stated status.

# Summary of changes for run c3c8a414-d7a6-43f1-9b08-b40c3d447171
ZETA_POLE_API_GAP

Added `RequestProject/RiemannBoundaryCellBridge.lean` and verified it builds. Integrated its zero-mass estimates into `RequestProject/Main.lean`, proving the T2 uniform dilation-sum bound and the corresponding `Estar` square-root bound. These declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

The remaining original contract cannot be proved literally because Mathlib’s `riemannZeta` assigns a finite point value at `1`. Thus the raw function
`riemannZeta (s + 1/2) * Mellin h (s + 1/2)`
need not be continuous at `s = 1/2`, even when `Mellin h 1 = 0`; a simple zero with nonzero derivative yields a nonzero punctured limit but point value zero. `RequestProject/Main.lean` contains verified general and shifted discontinuity theorems establishing this obstruction. Consequently T4, and hence T5 as stated at every point of the half-plane, requires a separately regularized value at the removable singularity; no Mathlib lemma can establish the false raw point-value claim.

`RESULT.md` contains exactly `ZETA_POLE_API_GAP`. The project builds successfully and its Lean sources contain no `sorry`, `admit`, added `axiom`, or `native_decide`.

# Summary of changes for run 042f25b8-6db5-48ec-b64e-b07571129925
RIEMANN_SUM_BOUNDARY_CELL_GAP

The exact missing statement is the finite right-endpoint mesh estimate

`‖u * ∑' n : ℕ+, h (n*u) - ∫ x in Set.Ioi 0, h x‖ ≤ u * (K*b + (‖h 0‖ + K*b) + ‖h b‖)`

under compact support in `[0,b]`, `0 < u`, and `LipschitzOnWith K h (Set.Ico 0 b)`. It must be assembled by telescoping over the mesh cells up to `Nat.ceil (b/u)`, estimating full interior cells by Lipschitz continuity, and isolating the unique terminal cell meeting `b` (including a possible endpoint sample `h b`). Mathlib supplies the constituent interval-integral and finite-sum estimates but no packaged lemma for this half-open-support boundary-cell argument, and the direct assembly did not close.

`RESULT.md` records the precise schematic statement and downstream APIs. `RequestProject/Main.lean` remains sorry-free and builds successfully; the repository was checked for forbidden declarations/tactics and all retained changes were committed and pushed.

# Summary of changes for run 55cd5d77-1311-4254-a722-7092d83c8e6f
RIEMANN_SUM_LIPSCHITZ_GAP

Implemented the corrected `ZetaMellinReg` definition and produced a self-contained, sorry-free Mathlib file. Proved:
- `Estar_eq_zero_of_gt`, the pointwise T1 tail statement for support in `[0,b]`;
- a general raw zeta-product discontinuity theorem at `w = 1` when the Mellin-type factor has a simple zero;
- its shifted form at `s = 1/2`.

The exact remaining gap is the quantitative right-endpoint Riemann-sum estimate for a complex-valued measurable bounded-variation function:
`‖u * ∑' n : ℕ+, h (n*u) - ∫ x in Set.Ioi 0, h x‖ ≤ u * (eVariationOn h Set.univ).toReal`
(up to endpoint constants). Mathlib provides `eVariationOn.sum_le`, `eVariationOn.sum_le_of_monotoneOn_Icc`, `eVariationOn.sum'`, and `BoundedVariationOn.dist_le`, but not the required bridge from these variation bounds to Lebesgue integrals/right-endpoint sums.

`RESULT.md` records the gap and the relevant APIs: `riemannZeta_residue_one` for the pole, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` for identity continuation, and the dominated differentiation-under-integral lemmas. The project builds successfully, contains no forbidden declarations/tactics, and all proved theorems have exactly the permitted axioms `[propext, Classical.choice, Quot.sound]`.
