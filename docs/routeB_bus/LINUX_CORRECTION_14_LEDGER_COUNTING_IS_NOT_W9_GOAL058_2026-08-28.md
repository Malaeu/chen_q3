---
TASK_ID: LINUX_SELF_CORRECTION_14
MODE: PAPER_ONLY
BODY: Linux-Claude
DATE: 2026-08-28
CORRECTS: 655c9831, sections 6 and 8
ACCEPTS_VERDICT: 9759aa5c
RH_CLAIM: false
---

# Correction 14 — counting names is not a dependency comparison

## 1. Withdrawn: the Schur candidate is a strictly smaller ledger

Report `655c9831` claimed the Schur/Feshbach split replaces four inputs with two
and is therefore a strict `W9` reduction. Refuted, on three separate grounds, all
correct.

**Output dimension is not dependency size.** Both new objects live on the central
`O(log m)` block, but both depend on the entire complement through
`C_{B'B'}^{-1}`. The complement did not leave the theorem; it moved inside an
inverse. I counted where the answer sits, not what the answer needs.

**The pair is stronger, not weaker.** `||P_B u|| >= ||f_B||/||S_B||` is a
*sufficient* condition for the central-mass bound. Proving both halves proves more
than was asked, so the ledger did not shrink even in the logical sense.

**The effective source is cancellation-sensitive.** The judge's falsifier settles
it concretely: on `q^perp = C^2` with `C = [[1,1/2],[1/2,1]]` and `B` the first
coordinate, `S_B = 3/4` is bounded and the raw central source component is `1`,
yet for `s_eps = (1, 2(1-eps))` the effective source is `f_B = eps`. Bounded Schur
complement and nonzero raw central source permit **arbitrary** cancellation
against the tail-return term. A lower envelope for `f_B` needs a new exact
source-correlation theorem and does not follow from the Schur identity.

## 2. Withdrawn: "writing `C` in blocks on `q^perp`"

The coordinate projections `P_B` and `P_{B'}` do not preserve `q^perp`, so
`q^perp` is not the asserted coordinate direct sum. The correct statement splits
the **full** carrier `H = B (+) B'`; the full positive-definite `C` has an
invertible principal `B'` block and the standard block solve then gives
`P_B u = S_B^{-1} f_B` with source `Q Phi`. The identity survives; my domain did
not.

## 3. Carrier guard

The window index must be `J_m^car = min(N_m, floor(delta L_m/(2 pi)))`. On the
selected schedule `N_m = m` and `L_m = log m`, so this equals my floor eventually
and the sampling inequality is **cofinally** correct, not an exact all-cell
identity. Recorded as stated rather than as a defect.

## 4. Ledger

Twenty-first forbidden move: **a `W9` comparison is about dependencies, not about
the number of names in a list.** Before claiming a smaller ledger, ask what each
new object needs, not where it lives. An object on a small block that inverts a
large block has not reduced anything.

Twenty-second: **a sufficient condition is not a reduction.** Replacing a target
by a pair whose conjunction implies it makes the work larger unless each half is
independently easier, which must be argued rather than assumed.
