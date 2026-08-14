# Goal 058 G3 — Mythos verdict on the Sturm source architecture

Date: 2026-08-14

Status: ARCHITECTURE ACCEPTED WITH SHARPENING; SOURCE PINS AND PROSHKA JUDGMENT PENDING

## Provenance

- Living Mythos chat:
  `https://claude.ai/chat/3bbe2272-8bc5-49ba-ab80-d723e24f3a8d`
- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Request pin: `4cb44f73ef2a8bf211f360730b6b0ed96b4633ba`
- Input boundary: the accepted regular-even Ferrers solution, actual derivative
  interface, simple interior zeros, and nonzero center value.
- Fixed nonclaims: no matching-root existence, physical scale, finite-Fourier
  eigenrelation, G3, G1, Route B promotion, or RH claim.

## Verdict

Mythos returned `ACCEPT` for the blocker decomposition, with one important
sharpening.  The load-bearing route is not an unconditional request to count
four zeros of a solution at an unspecified root.  It is an index theorem along
the parameter `Λ`:

1. establish Sturm comparison and monotonicity of the interior zero count as
   `Λ` increases for regular solutions at fixed quadratic coefficient;
2. characterize the third even regular root by zero count four;
3. only then identify the selected root-conditional solution with mode index 4
   and the third even mode `ψ₄`.

The currently accepted fields do not themselves supply this index theorem.

## Source candidates and honest pin boundary

Mythos named the following classical source families:

- Meixner--Schäfke, *Mathieusche Funktionen und Sphäroidfunktionen* (1954),
  section 3, for spheroidal eigenvalue ordering;
- Osipov--Rokhlin--Xiao, *Prolate Spheroidal Wave Functions of Order Zero*
  (2013), for the statement that the index-`n` eigenfunction has exactly `n`
  zeros in `(-1,1)`;
- Zettl, *Sturm--Liouville Theory*, for the singular oscillation framework;
- Courant--Hilbert I, chapter VI, for classical comparison.

No exact page/equation pins were supplied.  Mythos explicitly refused to
invent them and marked a source-pin packet as a prerequisite for the endpoint
crosswalk.  Therefore these references are candidates, not yet repository
source locks.

The endpoint convention that still needs proof is that the repository's
Ferrers-regular solution class is exactly the principal/Friedrichs branch for
the singular equation

```text
d/dx ((1 - x^2) f') + (Λ - K x^2) f = 0
```

on `(-1,1)`.

## Open transports

- `T1`: existence of the relevant matching roots;
- `T2`: dimensionless-to-physical scaling and the relation to `mProject`;
- `T3`: Ferrers regularity equals the principal/Friedrichs endpoint
  condition;
- `T4`: ordering of the roots and identification of the third even root;
- `T5`: a comparison interface in which the two solutions expose distinct
  `Λ` parameters while sharing the same `K` and interval data.

All five transports remain open.  In particular, a root-conditional selection
theorem must not be restated as root existence.

## Proposed bounded Lean kernel

Mythos proposed proving an interior comparison theorem on a compact subinterval
where the ODE is regular:

```lean
theorem mode4Ferrers_sturm_interior_comparison
    (S₁ S₂ : Mode4FerrersRegularEvenProlateSolution ...)
    (hΛ : Λ₁ < Λ₂)
    {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ Set.Ioo (-1 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Ioo (-1 : ℝ) 1)
    (hlt : x₁ < x₂)
    (hz₁ : S₁.toFun x₁ = 0)
    (hz₂ : S₁.toFun x₂ = 0) :
    ∃ y ∈ Set.Ioo x₁ x₂, S₂.toFun y = 0
```

The suggested mechanism is a Wronskian/Picone identity for
`p(x) = 1 - x^2`, followed by a sign argument and the intermediate value
theorem.  This head is a candidate only: Proshka must check the shared-parameter
binders, whether consecutive zeros or a no-zero hypothesis is required, and
whether the current structure exposes enough actual-derivative data.

## Aristotle recommendation from Mythos

Mythos judged Aristotle appropriate for the bounded interior-comparison kernel,
not for the entire singular endpoint and indexing theorem.  The proposed gates
were:

- strict parameter inequality is load-bearing;
- both endpoints of the comparison interval remain strictly inside `(-1,1)`;
- the direction of comparison is planted against a sign-flip mutant;
- axiom profile remains `[propext, Classical.choice, Quot.sound]`;
- stop if the actual derivative interface or separate `Λ` parameters are not
  available.

No Aristotle submission is authorized by this report alone.  It awaits
Proshka's exact-head judgment and the source-pin prerequisite decision.

## Separation from the Fourier wall

This architecture can advance only the ODE-side, root-conditional selection of
mode 4.  It contributes nothing by itself to the restricted finite-Fourier
eigenrelation.  The latter remains a separate integral-operator/source
constructor obligation.

## Nonclaims

- `NO_EXACT_SOURCE_PAGE_PINS`
- `NO_ENDPOINT_CROSSWALK`
- `NO_STURM_COMPARISON_THEOREM_YET`
- `NO_ZERO_COUNT`
- `NO_ORDERED_PSI4_IDENTIFICATION`
- `NO_MATCHING_ROOT_EXISTENCE`
- `NO_PHYSICAL_SCALE`
- `NO_FINITE_FOURIER_EIGENRELATION`
- `NO_G3`
- `NO_G1`
- `NO_ROUTE_B_PROMOTION`
- `NO_RH`
