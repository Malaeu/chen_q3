# Result

`RIEMANN_SUM_LIPSCHITZ_GAP`

The corrected formulation was used: `ZetaMellinReg` assigns the derivative of the Mellin transform at the pole, and the support interval in the proved tail lemma is `[0,b]`.

The full requested T1–T5/PL2 package was not completed. The exact blocking library-level step is a quantitative right-endpoint Riemann-sum estimate for a **complex-valued measurable function of bounded variation**:

```lean
‖u * ∑' n : ℕ+, h (n * u) - ∫ x in Set.Ioi 0, h x‖
  ≤ u * (eVariationOn h Set.univ).toReal
```

(up to a harmless endpoint constant), for `u > 0` and compact support. Mathlib supplies the primitive variation bounds `eVariationOn.sum_le`, `eVariationOn.sum_le_of_monotoneOn_Icc`, `eVariationOn.sum'`, and `BoundedVariationOn.dist_le`, but no theorem connecting those bounds to Lebesgue integrals/right-endpoint Riemann sums in the required form. Assembling that bridge from the primitive definitions remains the gap.

`RequestProject/Main.lean` contains no `sorry`, `admit`, new `axiom`, or `native_decide`. It proves:

* the pointwise T1 tail statement `Estar_eq_zero_of_gt` for support in `[0,b]`;
* a general theorem showing that the raw product `riemannZeta w * M w` is discontinuous at `w = 1` whenever `M 1 = 0` and `M` has nonzero derivative there;
* the shifted version at `s = 1/2`;
* the corrected definition `ZetaMellinReg`.

All three proved theorems use exactly `[propext, Classical.choice, Quot.sound]`.

Relevant Mathlib APIs located during the work:

1. Zeta pole: `riemannZeta_residue_one`; also `tendsto_riemannZeta_sub_one_div`, `differentiableAt_riemannZeta`, and `HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div`.
2. Identity theorem: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
3. Differentiation under the integral: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` and `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`.
