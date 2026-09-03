# MYTHOS PAPER NOTE — STEP 1 (LIMIT IDENTIFICATION), written 2026-09-03 AFTER registration of P_STEP1_NO_UNIQUENESS (p=0.75 on 2026-09-02)

```yaml
STATUS: MYTHOS_PAPER_NOTE
AUTHOR: Mythos (Claude)
DATE: 2026-09-03
REPO: Malaeu/chen_q3
BRANCH: rh_clean
SOURCE_BASE_COMMIT: 2bb8db37baf532b41a502269a2e2d420cb41ca6c
RELATES_TO: REQ-2026-09-03-KILLPLAN
SCORING_ROLE: EVIDENCE_ONLY (not part of the registered prediction text)
VERIFIER: NONE (paper; Proshka adjudicates)
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
DB-SEARCH: git grep -n -i "eqOn_of_preconnected_of_frequently_eq\|identity theorem" FETCH_HEAD -- q3.lean.aristotle/Q3 -> not run by Mythos; Codex to run (see task).
```

## 1.1 Abstract identification is RH-circular (claim, to be audited)

Setting. `L` is a cluster limit on `centeredCriticalStrip` of the ground family:
holomorphic, locally not identically zero, real zeros (Hurwitz), even, and
`L(a) = centeredXi(a)` at one anchor `a`; order <= 1 if uniform bounds hold.

Claim. No list of limit-stable properties that `centeredXi` satisfies can force
`L = c * centeredXi * gamma` with `gamma` zero-free on the strip, unless the list
already decides RH.

Argument. Suppose RH fails and `rho` is a non-real zero of `centeredXi` in the
strip. Let `Xi_real` be the canonical product over the real zeros `x` of
`centeredXi` only (pairs `(1 - z^2/x^2)`; converges since `sum 1/x^2 < infinity`
by the zero-counting bound). Then `Xi_real` is entire, even, real on the real
axis, of order <= 1, has only real zeros, and can be normalized at `a` (after a
nonzero constant). It satisfies every property in the list, but `rho` is not a
zero of `Xi_real`, so `zeros(centeredXi) ⊄ zeros(Xi_real)` and the roof
transfer fails for it. Hence any property list that separates `centeredXi`
from `Xi_real` must "see" `rho`, i.e. decides RH. Conversely, if RH holds, then
`Xi_real = centeredXi` up to a zero-free factor and no identification is
needed. So abstract identification works iff RH: circular.

Prediction P_STEP1_NO_UNIQUENESS: on paper CONFIRMED by this argument; official
fate is set only by Proshka's verdict on REQ-2026-09-03-KILLPLAN.

## 1.2 What can identify: the identity theorem (anchor exists)

If `L` is holomorphic on the connected strip and agrees with `centeredXi` on a
set with an accumulation point inside the strip (any real interval, any
convergent sequence), then `L = centeredXi` on the strip. Mathlib carries this
(the `AnalyticOn*.eqOn_of_preconnected_of_frequently_eq` family; exact
identifier to be confirmed by Codex). No new mathematics.

## 1.4 Consequence for the roof type

`SlotAnchor` (CanonicalRHRouteSkeleton.lean lines 57-60) demands agreement at
ONE point. One point never yields identification (needs an accumulation point).
Therefore `hanchor` is structurally incapable of identification work in
`rh_of_canonical_strip_slots`; all identification was carried by `SlotS2`
(lines 122-129), which is why S2 was found OVERSTRONG in
PROSHKA_VERDICT_EXACT_ROOF_PORT_TO_SUPPLIER_LEDGER_2026-09-01.md.

## 1.3 The remaining question (open, source check)

For 1.2 to fire, the construction must supply agreement of the limit with
`centeredXi` on a set with an accumulation point. Question for the source:
does `proposition59CCMTransform (ccmL m) N xi_R` (G6N1SelectedFerrersGroundProposition59RealZeros.lean)
agree with `centeredXi` structurally anywhere — interpolation at nodes that
become dense on the critical line, exact moment identities implying agreement,
or any other exact equality with a limit point?

- If YES: the wall compresses to NORMALITY of the ground family on the strip
  (uniform bounds on compacts). Classical territory.
- If NO: identification equals CCM Input B; the compactness angle is dead in
  full; only the rate angle remains. Step 1 closes.

## Registered prediction for 1.3 (K6, before the source check)

P_STEP1_3_NO_STRUCTURAL_AGREEMENT: the P59 transform has no built-in exact
agreement set with centeredXi having a limit point in the strip; probability
0.65; fate PENDING.
