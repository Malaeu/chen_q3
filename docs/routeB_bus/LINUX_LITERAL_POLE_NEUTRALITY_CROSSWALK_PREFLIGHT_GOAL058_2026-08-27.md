---
TASK_ID: GOAL058_SELECTED_FERRERS_LITERAL_POLE_NEUTRALITY_CROSSWALK_PREFLIGHT
MODE: PAPER_AND_SOURCE_READ_ONLY
BODY: Linux-Claude
DATE: 2026-08-27
RESPONDS_TO: d9802775
DISCRIMINATOR: HOLD
RESULT_CODE: POLE_FUNCTIONAL_EXPLICIT_BUT_COFINAL_SIZE_UNCONTROLLED
LEAN_EDIT: false
NUMERICS: none
ARISTOTLE: false
CODEX: false
RH_CLAIM: false
CLOSES:
  - POLE_NEUTRALITY_STATED_ONLY_IN_GROSKIN_COORDINATES
OPENS:
  - MODE_INDEX_DECAY_OF_THE_SELECTED_FERRERS_ROW
---

# Literal pole-neutrality crosswalk

## 0. Result

The pole-neutral condition crosswalks to a single, clean statement about our own
source objects, with no reference to Groskin's coordinates:

    the selected row is pole-neutral
      <=>  sum_n q_n * ccmW02Entry L n 0 = 0,

that is, **the trial row is orthogonal to the center column of the pole block**.

Whether the literal row satisfies it does not follow from anything banked. The
decisive missing input is mode-index decay of `q`, and the bank supplies only
`l^2` normalization plus a center-coefficient floor. Discriminator: HOLD, exactly
the judge's `P_POLE_NEUTRAL_2` branch in shape, though the size is not yet
controlled in either direction.

## 1. Crosswalk of the condition

Groskin's hyperplane, in his even-sector coordinates, is

    v_0/beta^2 + sqrt 2 * sum_{k=1}^{N} v_k/(k^2+beta^2) = 0,   beta = L/(4 pi).

His embedding is `u_0 = v_0`, `u_k = u_{-k} = v_k/sqrt 2`. Substituting,

    v_0/beta^2 + sqrt 2 * sum_{k>=1} (sqrt 2 u_k)/(k^2+beta^2)
      = u_0/beta^2 + 2 * sum_{k>=1} u_k/(k^2+beta^2)
      = sum_{n=-N}^{N} u_n/(n^2+beta^2),

the last step using `u_{-n} = u_n`. So on the full carrier the condition is simply

    sum_{n=-N}^{N} q_n / (n^2 + beta^2) = 0.                             (P)

Now convert to source units. With `beta^2 = L^2/(16 pi^2)`,

    1/(n^2 + beta^2) = 16 pi^2 / (L^2 + 16 pi^2 n^2),

and from the Lean source at the center (node `ccmW02Entry_center`, commit
`2aaff3e7`),

    ccmW02Entry L n 0 = 32 L sinh^2(L/4) / (L^2 + 16 pi^2 n^2).

Therefore

    sum_n q_n/(n^2+beta^2)
      = ( pi^2 / (2 L sinh^2(L/4)) ) * sum_n q_n * ccmW02Entry L n 0,

and the prefactor is finite and nonzero for `L > 0`. Condition (P) is thus
**equivalent** to

    sum_n q_n * ccmW02Entry L n 0 = 0.                                   (P')

This is the requested literal crosswalk. Note what it says: pole-neutrality is
orthogonality of the trial to the center column of the pole block — a statement
entirely inside our own source, using no Groskin object.

Two corollaries of (P'), recorded because they connect existing pieces:

- Since `ccmBetaScalar m n = n * ccmWeilTauN1 m n 0` and the pole part of that is
  `n * ccmW02Entry L n 0`, condition (P') is the statement that the trial has
  vanishing *inverse-mode-weighted* pairing with the pole part of `beta`,
  together with the `n = 0` term. Pole-neutrality and the `beta` construction
  read the same column, with different weights in `n`.
- If (P') holds then, by Groskin Corollary 2.7, `g_q(i/2) = 0` and the entire pole
  block drops out of the pairing, not merely its diagonal.

## 2. What the literal row is, from source

`selectedFerrersFiniteCCMRow P k j = c_n(index k, prolateCombination(pair k), ..., mode j)`
(`G6N1SelectedFerrersFiniteCCMSourceRow.lean:88`), and
`c_n i h ... n = inner (V_n_m i n) (kTrial_m_N i h ...)`
(`D0KTrialStage3.lean:81`). So `q_n` is the `n`-th coefficient of the normalized
projected trial in the orthonormal basis `V_n`.

The trial is built from
`prolateCombination P x = (I4 * h0 x - I0 * h4 x) / sqrt(I0^2 + I4^2)`
(`ProlateLayer.lean:95`), with `I0 = integral h0` and `I4 = integral h4`
(`ProlatePair.I0_eq_integral`, `I4_eq_integral`).

**The functional the construction annihilates is the integral.** By design,
`integral (prolateCombination P) = (I4 * I0 - I0 * I4)/norm = 0`. That is the
selection's built-in orthogonality, and it is the *unweighted* functional.

Condition (P) is a **Cauchy-weighted** functional, weight `1/(n^2+beta^2)`.
Nothing in the construction mentions it. The two functionals coincide only if a
same-family theorem forces it, and no such theorem exists in the catalogue —
asked this session, no supplier returned.

The row is even (`h0`, `h4` are even by `h0_even`, `h4_even`), so
`q_{-n} = q_n` and (P) reduces to `q_0/beta^2 + 2 sum_{n>=1} q_n/(n^2+beta^2) = 0`.

## 3. Why it does not decide, and what would

Two banked facts bear on (P), and together they fall short by an explicit margin.

**Center term, bounded below.**
`selectedFerrersFiniteCCMCenterCoefficient_eventually_inv_log_floor_of_modeAndChiRates`
(`G6N1SelectedFerrersCenterCoefficientFloor.lean:1081`, kernel-green) gives
`|q_0| >= c / log m` eventually. Hence

    | q_0 / beta^2 |  =  |q_0| * 16 pi^2 / L^2  >=  16 pi^2 c / L^3.

**Off-center tail, bounded above by normalization only.** With `||q||_2 = 1` and
Cauchy-Schwarz,

    | sum_{n != 0} q_n/(n^2+beta^2) |
      <= ( sum_{n != 0} (n^2+beta^2)^{-2} )^{1/2}
      <= ( 2 * sum_{n>=1} n^{-4} )^{1/2} = ( pi^4/45 )^{1/2} = 1.4713...

So the guaranteed center contribution is of order `1/L^3` while the only
available tail bound is `O(1)`, larger by a factor `L^3`. The comparison decides
nothing: the tail could cancel the center exactly, or swamp it, or be far
smaller.

**The missing input is mode-index decay of `q`.** Any bound of the form
`|q_n| <= f(n)` with `sum_{n != 0} f(n)/n^2 = o(1/L^3)` would settle (P) in the
negative and give FAIL. None exists. The bank controls `q` in `l^2` and at the
center, and nowhere in between.

This is the same *type* of gap the judge already carries as
`WEIGHTED_MODE_MOMENT_BOUND_FOR_GRAPH_RESOLVENT_VECTOR`, stated there for
`x = C^{-1} kappa` and here for `q`. Two different vectors, one missing kind of
supplier. Recording that as the structural observation of this preflight: the
pole-neutral route is **not** independent leverage — it consumes exactly the
supplier the regularity route also needs.

## 4. Guards observed

- The selected row was **not** modified, and no projection onto the hyperplane
  was performed or proposed. Verdict `d9802775` forbids post-hoc projection and
  that is respected; the only question asked here is whether the literal row
  already satisfies (P).
- No numerics. The two numbers above (`pi^4/45` and the inverse-log floor) are a
  closed-form series value and a banked theorem.
- No component split: (P') is a single pairing against one column, not a
  separated estimate of a ledger.

## 5. Next load-bearing gap

    MODE_INDEX_DECAY_OF_THE_SELECTED_FERRERS_ROW

stated as: a supplier bounding `|q_n|` as a function of `n` along the selected
schedule, strong enough that `sum_{n != 0} |q_n|/n^2 = o(1/(log m)^3)`. With it,
(P) resolves in the negative and the pole-neutral route closes honestly. Without
it, (P) is undecided in both directions and no work downstream of it is safe.
