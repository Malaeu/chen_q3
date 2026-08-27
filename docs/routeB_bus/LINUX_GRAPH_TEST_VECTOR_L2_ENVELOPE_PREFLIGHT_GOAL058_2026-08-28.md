---
TASK_ID: GOAL058_SELECTED_FERRERS_GRAPH_TEST_VECTOR_L2_COMPACT_ENVELOPE_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
RESPONDS_TO: 4049c26e
DISCRIMINATOR: HOLD
RESULT_CODE: GRAPH_INVERSE_BOUND_REDUCED_TO_FLOOR_SOURCE_ALONE
LEAN_EDIT: false
NUMERICS: corroboration only, declared
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - P59_KERNEL_ROW_NORM_AS_AN_UNKNOWN_INPUT
OPENS: []
---

# Graph test vector envelope: one input closed in exact form, one left

## 0. Result

Of the two inputs the verdict named, the **P59 kernel row norm is closed
exactly**, not estimated:

    || kappa(z) ||_2^2  =  L^2 * sinh( L * Im z ) / ( L * Im z )   on the full lattice,

with the right-hand side an upper bound on our finite carrier. At `Im z = 0` the
value is exactly `L^2`. The whole envelope therefore reduces to the complement
floor alone, and the shelf returns no supplier for it. Discriminator: HOLD, the
verdict's middle branch, with the kernel half retired.

## 1. Coercivity chain, on paper

Let `C = Q (K - eps I) Q + P`, `P = q q^*`, `Q = I - P`, `||q||_2 = 1`, `K`
Hermitian, `eps <= a`, and let the complement floor hold: for every `w` with
`<q,w> = 0`,

    beta * ||w||^2 <= Re < w, (K - a I) w >.

Decompose `y = y_par + y_perp` with `y_par = <q,y> q` and `y_perp = Q y`. Then

    Re <y, C y> = Re <y_perp, (K - eps I) y_perp> + |<q,y>|^2
                = Re <y_perp, (K - a I) y_perp> + (a - eps) ||y_perp||^2 + ||y_par||^2
                >= beta ||y_perp||^2 + ||y_par||^2
                >= min(beta, 1) ||y||^2.

From `||C y|| ||y|| >= |<y, C y>| >= min(beta,1) ||y||^2` we get
`||C y|| >= min(beta,1) ||y||`, and setting `y = C^{-1} kappa`,

    || C^{-1} kappa ||_2 <= || kappa ||_2 / min(beta, 1).                  (*)

This is the verdict's generic route, written out. Its hypothesis is exactly the
hypothesis of the banked `trialGraphOperator_posDef`
(`G6N1SelectedFerrersFiniteAssetBank.lean:209`), which consumes the same floor
`hfloor` and the same `eps <= a`. That theorem delivers `PosDef`; the
quantitative constant `min(beta,1)` is the extra content of (*) and is not
banked.

## 2. The kernel row in closed form

From source: `proposition59Numerator L z = 2 sin(z L/2)`,
`proposition59Pole L k = 2 k pi / L`, and
`proposition59PoleKernel L k = dslope (proposition59Numerator L) (proposition59Pole L k)`
(`Proposition59EntireTransform.lean:13,17,33`). Since the numerator vanishes at
every pole (`proposition59Numerator_at_pole`, line 20), for `z` off the lattice

    kappa_k(z) = 2 sin(z L/2) / ( z - 2 k pi / L ).

Substituting `w = z L / 2` turns this into

    kappa_k(z) = L * sin(w) / ( w - k pi ),

whose removable value at `w = k pi` is `L cos(k pi)`, matching the banked
`proposition59PoleKernel_at_pole`. So the whole row is one scalar times a pure
Cauchy vector on the shifted lattice, which is the same structure the corridor
already uses for the consumer error.

**Exact norm.** With `w = u + i v`, two classical identities,

    sum_{k in Z} 1/((u - k pi)^2 + v^2) = (1/v) * sinh(2v)/(cosh(2v) - cos(2u)),
    |sin w|^2 = ( cosh(2v) - cos(2u) ) / 2,

multiply to a quantity independent of `u`:

    || kappa(z) ||_2^2 = L^2 * sinh(2 v) / (2 v),   v = L * Im(z) / 2,

that is `L^2 * sinh(L Im z)/(L Im z)`. At `Im z -> 0` the limit is `L^2`, the
Shannon sampling identity; there is no pole difficulty anywhere, consistent with
`kappa` being entire. Our carrier is `|k| <= N`, a sub-sum of a non-negative
series, so the closed form is an upper bound for us.

Corroboration, declared and not load-bearing: evaluated at `L = 4, 8`,
`Im z = 0.05, 0.3, 1.0`, `Re z = 0, 0.37, 1.1` with the lattice truncated at
`|k| <= 4000`; ratios to the closed form between `0.99980` and `0.99999996`,
the gap shrinking with the truncation as it must. On the real axis the numeric
value is `L^2` to eight digits.

**Compact form.** On `|Im z| <= sigma`,

    || kappa(z) ||_2 <= L * sqrt( sinh(L sigma) / (L sigma) )  ~  sqrt( L/(2 sigma) ) * m^{sigma/2},

since `L = log m`. The `m^{sigma/2}` growth is exactly the compact envelope shape
the corridor has carried since the `lambda^sigma` ledger; it is now derived rather
than assumed, with the constant explicit.

## 3. What remains

Combining (*) with section 2, on `|Im z| <= sigma`:

    || x_k(z) ||_2 <= sqrt( L / (2 sigma) ) * m^{sigma/2} / min(beta_k, 1).

Everything on the right is explicit except `beta_k`. Asked of the shelf this
session under `complement floor` and under
`SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR`: **no supplier returned**. The
catalogue holds neighbouring floors — `D0AnchorFloorFromUnprojectedCentralMass`,
`D0AnchorFloorFromUnprojectedMassNormRatio`, the perturbative true-gap floors,
the mode-4 Hermitian Schur lower envelope — none of which is a floor for the
`q`-orthogonal complement at the Rayleigh shift. The assembly catalogue lists
`SIMPLE_EVEN_GROUND_TO_REAL_ZEROS` step 4 as `[READY]` for the
complement/lattice factor, which is a different object.

So the envelope reduces to one scalar per cell, and that scalar is one of the two
floors carried open since the corridor opened.

## 4. Guards

- No new supplier minted; section 3 names an existing open item rather than a new
  one.
- The quantitative constant `min(beta,1)` is flagged as **not banked**; only
  `PosDef` is.
- Numerics corroborate a closed form derived independently; nothing in sections
  1-3 rests on them.
- Correction 10 (`LINUX_CORRECTION_10_ENERGY_IS_UNPROJECTED_GOAL058_2026-08-28.md`)
  withdraws the energy identity of `ad621220` section 3; nothing above uses it.

## 5. Next load-bearing gap

    SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR

as the single remaining input of the graph envelope: an eventual `beta_k > 0`,
with a rate, for the `q_k`-orthogonal complement of `K_k - a_k I` along the
selected schedule. With it, `|| x_k(z) ||_2` is explicit; without it, nothing
downstream of the Duhamel regularity side can be closed.
