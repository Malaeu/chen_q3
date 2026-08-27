---
TASK_ID: LINUX_SELF_CORRECTION_5
MODE: PAPER_ONLY
BODY: Linux-Claude
DATE: 2026-08-27
CORRECTS: c1e5f00f (LINUX_CUT_TREE_AND_RICCI_SIGN_PREFLIGHT_GOAL058_2026-08-27.md), section RICCI_DOOB_SIGN_FRUSTRATION
ACCEPTS_VERDICT: b1c580ca
STATUS: MY_CLAIM_WITHDRAWN
RH_CLAIM: false
---

# Correction 5 — oddness of beta does not imply sign frustration

## 1. The refutation is accepted in full

Report `c1e5f00f` claimed `RICCI_DOOB_SIGN_FRUSTRATION_FATAL`, proved by parity.
The judge refuted it with an exact plant, nodes `[-1, 0, 1]`, `beta_n = -n`, for
which every off-diagonal entry equals `-1` and the gate passes under the identity
switch. The plant is odd, vanishes at zero, and is not identically zero — it
satisfies every hypothesis I used. The claim is withdrawn.

## 2. Where exactly the argument broke

The triangle criterion itself is correct and survives. For `i < j < k`,

    sign( K_ij K_jk K_ki ) = sign[ (beta_j - beta_i)(beta_k - beta_j)(beta_k - beta_i) ],

which is `+1` exactly when the ordering of the three values is an **even**
permutation of increasing order, and `-1` when it is odd.

The broken step was the next sentence. I wrote: "take any `n > 0` with
`beta_n > 0`; such an `n` exists because beta is not identically zero." That is
a non sequitur. Oddness gives `beta_{-n} = -beta_n`; it does not give a positive
value at a positive index. If `beta_n < 0` for every `n > 0` — exactly the
plant's situation — the triple `(-n, 0, n)` reads `+, 0, -`, which is decreasing,
and the gate is not violated by it.

The missing lemma has a name and is not proved anywhere in the corpus:

    SOURCE_BETA_POSITIVE_AT_A_POSITIVE_MODE.

I asserted it from the oscillatory shape of the prime sum without deriving it.
That is the same failure mode as correction 4: an unproved structural intuition
carried into a report as if it were source-locked.

## 3. What the corrected criterion actually demands

The gate requires the odd sign for **every** triple `i < j < k`. In particular
`beta_i < beta_j < beta_k` is forbidden, so a necessary condition is:

    beta has no increasing subsequence of length three.

The condition is strictly stronger than "no ascending run", and strictly weaker
than "beta is monotone decreasing". A witness that it is weaker than monotone:
`(0, 2, 1, 1/2)` at consecutive nodes passes all four triples yet is not
monotone. So the natural shortcut "gate holds iff beta is decreasing" is also
wrong and must not be substituted for the real criterion.

## 4. The cheapest decisive probe that remains

Because "no increasing subsequence of length three" forbids in particular three
consecutive ascending values, one ascending run of length three anywhere in the
lattice kills the gate. In terms of the first difference `(Delta beta)_n =
beta_{n+1} - beta_n`, the gate requires:

    (Delta beta)_n > 0  and  (Delta beta)_{n+1} > 0  never occur together.

That is a statement about the source object alone, with no consumer, no rate and
no numerics in it. It is the correct replacement for my parity argument and it is
cheaper than the argument it replaces.

Structure of the question, stated without asserting the answer: `Delta beta`
carries a `W02` contribution that is smooth in `n`, an archimedean contribution,
and a prime contribution which is a finite cosine sum damped by the factor
`sin( pi log q / log m )` at each frequency. Whether two consecutive positive
first differences occur depends on whether the oscillating part ever exceeds the
smooth part over two adjacent steps. I do not claim to know which way it goes.

## 5. Ledger entry

Forbidden move recorded, sixth entry: **an existence claim about the sign of a
source object is not supplied by a symmetry of that object.** Oddness fixes the
relation between `beta_n` and `beta_{-n}`; it says nothing about which of the two
is positive. Before using "there exists a mode where the source is positive",
either cite a declaration or prove it.

Standing: `SELECTED_CCM_RICCI_DOOB_ACTUAL_SIGN_FRUSTRATION` is OPEN, the
classical Markov/Ricci route is NOT killed, and prediction `P_RICCI_2` remains
untested rather than confirmed.
