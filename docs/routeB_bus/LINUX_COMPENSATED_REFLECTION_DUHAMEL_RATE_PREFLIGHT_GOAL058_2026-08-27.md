---
TASK_ID: GOAL058_SELECTED_FERRERS_COMPENSATED_REFLECTION_DUHAMEL_RATE_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-27
RESPONDS_TO: 979feca5
DISCRIMINATOR: HOLD
RESULT_CODE: COMPENSATED_FUNCTIONAL_AND_ENERGY_CROSSWALK_CLOSED_WITHOUT_X_ENVELOPE
LEAN_EDIT: false
NUMERICS: corroboration only, declared; every display below is closed-form algebra
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - TRIAL_MODE_ENERGY_AS_A_NEW_SUPPLIER
  - REFLECTION_FUNCTIONAL_WITHOUT_ENDPOINT_COMPENSATION
OPENS: []
---

# Compensated reflection and the Duhamel rate

## 0. Result

Two of the three carried-open items collapse into objects that already exist.

The mode-energy supplier I proposed is **not new**: it is the existing contract
`SelectedPhysicalFourierEnergyControl`, and the conversion to `||N q||_2` is an
exact identity, not an estimate. The compensated reflection functional is
well-defined with an **m-independent** residue `1/(2 pi)` at each endpoint, and
the two residues are equal and opposite.

What does not close is the one item the judge already named as mine to fix: the
compact `L^2` envelope of `x = C^{-1} kappa(z)`. Discriminator: HOLD.

## 1. The three repairs of `979feca5`, accepted

**Periodic fold.** Accepted, and it makes the match cleaner than I reported. The
raw `W02` density lives on `t > 0` while the test function has period `2 pi`, so
the density must be folded. Summing the geometric series with `a = L/(4 pi)`,
`2 pi a = L/2`:

    sum_{j>=0} exp(-a(t + 2 pi j)) = exp(-a t)/(1 - exp(-L/2)) = exp(-a t) * sqrt m/(sqrt m - 1).

Since `sqrt m - 2 + 1/sqrt m = (sqrt m - 1)^2 / sqrt m`, the folded density is

    [L/(2 pi^2)] * (sqrt m - 1)^2/sqrt m * sqrt m/(sqrt m - 1) * exp(-a t)
      = [L/(2 pi^2)] * (sqrt m - 1) * exp(-a t),

exactly as the verdict states. Against the reflected continuous prime main term
`[L sqrt m/(2 pi^2)] exp(-a t)`, the difference is **exactly**

    - [L/(2 pi^2)] exp(-a t) dt,

with no `1/sqrt m` remainder. My `-2 + 1/sqrt m` was an artefact of comparing an
unfolded density, and report `535074f7` had already verified the fold — I had the
piece and did not use it. Recorded again as the same failure mode.

The guard of the verdict is kept: this is an exact statement about the
**continuous main model**, not a bound on the arithmetic discrepancy. The
Stieltjes remainder `d psi - dx`, the `1..2` lower-endpoint correction and the
archimedean endpoint functional are all still outside it.

**Not a finite measure.** Accepted, and the residue is computable exactly.
Changing variables `t = 2 pi x / L` in the archimedean ledger of `2aaff3e7` gives

    d mu_arch(t) = [L/(4 pi^2)] * exp(L t/(4 pi)) / sinh(L t/(2 pi)) dt.

As `t -> 0`, `sinh(L t/(2 pi)) ~ L t/(2 pi)`, so

    d mu_arch(t) ~ dt/(2 pi t),

which confirms the verdict's estimate and adds that the coefficient is
`1/(2 pi)`, **independent of m and of the schedule**. So `mu` is not finite,
`nu_m([0,t])` is not defined, and total mass is not an available notion. Both
forbidden objects are withdrawn from my cross-check report.

**`||x||_2` is not free.** Accepted without reservation. `||q||_2 = 1` holds for
the literal selected row; `x = C^{-1} kappa(z)` is the output of a linear solve
and carries no normalization. I conflated the two vectors.

## 2. The compensated functional

Under `R(t) = 2 pi - t` the origin maps to `2 pi`, so `nu = mu - R_* mu` carries

    + dt/(2 pi t)          at t -> 0,
    - dt/(2 pi (2 pi - t)) at t -> 2 pi,

two simple singularities with **equal and opposite residues** `1/(2 pi)`. The
test function vanishes at both ends to first order, `G(0) = G(2 pi) = 0` with
`G(t) = t * sum_i omega_i n_i + O(t^3)`, so each product is bounded and the
pairing converges absolutely. The legal object is therefore

    Phi_m(G) = integral_{(0, 2 pi)} G d nu_m,

a functional on the class of Lipschitz tests vanishing at both endpoints, and
**not** an integral against a finite signed measure. Integration by parts, if
used, must go against the compensated primitive

    F_m^comp(t) := lim_{eps -> 0} [ nu_m([eps, t]) - (1/(2 pi)) log(1/eps) ],

whose existence is exactly the statement that the residue is `1/(2 pi)`. The
naive `nu_m([0,t])` never exists.

## 3. Catalogue crosswalk — the supplier already exists

The verdict forbade minting `TRIAL_MODE_ENERGY_BOUND_ALONG_THE_SCHEDULE` before
checking the existing ledgers. Checked. It must not be minted, because it is
already there and the conversion is exact.

From `D0PstarPhysicalFourierEnergyControl.lean`:

    physicalFourierFrequency i n  = 2 pi n / L_m i                       (line 25)
    physicalFourierWeight i n     = |physicalFourierFrequency i n|^2     (line 30)
    physicalFourierCoefficient i f n = inner (V_n_m i n) f               (line 35)
    physicalFourierEnergy i f     = sum_n weight(n) * ||coefficient(n)||^2 (line 40)

The coefficient is the **same formula** as `c_n` in `D0KTrialStage3.lean:81`, so
`physicalFourierCoefficient` applied to the selected trial *is* our `q_n`.
Therefore, identically,

    physicalFourierEnergy = sum_n (4 pi^2 n^2 / L^2) |q_n|^2 = (4 pi^2/L^2) * ||N q||_2^2,

that is

    ||N q||_2 = (L / (2 pi)) * sqrt( physicalFourierEnergy ).

`SelectedPhysicalFourierEnergyControl` (line 66) asserts summability of each row
together with `IsBoundedUnder` on the energies along the schedule. Under it,

    ||N q||_2 = O(L) = O(log m).

So the mode energy of the trial is supplied by an existing named contract with an
exact conversion, and my proposed supplier is withdrawn as a duplicate.

**Status of that contract, stated plainly.** It is a `Prop`, consumed as a
hypothesis (`hEnergy` at line 181), and the first-order budget route explicitly
does not use it: `G6N1SelectedFerrersFirstOrderBudgetApplication.lean:121` says
"`SelectedPhysicalFourierEnergyControl` is nowhere required", and
`D0PstarFirstOrderProjectionTailReceiver.lean:22,174` say it is "untouched". So
the contract exists, the conversion is exact, and the contract is **not
discharged**. It is a named open supplier, not a proved one — which is a strictly
better position than an unnamed missing one.

## 4. What the rate now needs

Assembling: `Phi_m(G)` is bounded by a regularity norm of `G` times a compensated
discrepancy norm of `nu_m`. From the Duhamel/Volterra crosswalk ratified in
`979feca5`, the regularity side uses only

    ||x||_2,   ||q||_2 = 1,   ||N q||_2 = (L/(2 pi)) sqrt(energy),

with no carrier-dimension factor, since `<eta, U_t q>` enters as a trigonometric
polynomial whose `L^2` norm in `t` is `sqrt(2 pi) ||q||_2`.

Three inputs remain, and none is supplied:

1. `GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE` — an explicit compact envelope for
   `||x_k(z)||_2`, from the graph floor and the P59 kernel envelope. This is the
   judge's item and it is the binding one.
2. `SelectedPhysicalFourierEnergyControl` discharged, or a conversion from the
   first-order coefficient ledger that is discharged.
3. `COMPENSATED_REFLECTION_DISCREPANCY_SOURCE_BOUND` — a bound on `Phi_m` at
   consumer strength, which needs the Stieltjes remainder `d psi - dx` and the
   two corrections named in the verdict's `remaining_source_terms`, not only the
   continuous main model.

Item 3 is where the arithmetic re-enters. Items 1 and 2 are about objects we
construct. The corridor has not previously been in a position where two of three
open items are ours rather than the primes'.

## 5. Guards

- No component split: `W02`, arch and prime are compared only inside the single
  reflected functional; their individual masses appear nowhere in section 4.
- No forbidden object: `nu_m([0,t])` and "total mass zero" are withdrawn.
- No new supplier minted: section 3 retires my own proposal in favour of an
  existing contract.
- Numerics: the fold arithmetic of section 1 is closed-form
  (`(sqrt m - 1)^2/sqrt m * sqrt m/(sqrt m - 1) = sqrt m - 1`); it was also
  checked numerically at `m = 10^2, 10^4, 10^8, 10^16` under the owner's standing
  verification instruction, agreement to float precision, DIAGNOSTIC_NEVER_A_PROOF.

## 6. Next load-bearing gap

    GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE

for `x_k(z) = C_k^{-1} kappa_k(z)`, uniformly on each fixed compact in `z`, from
the banked graph floor and the P59 pole-kernel envelope. Everything else in the
regularity side is now either an identity or a named existing contract.
