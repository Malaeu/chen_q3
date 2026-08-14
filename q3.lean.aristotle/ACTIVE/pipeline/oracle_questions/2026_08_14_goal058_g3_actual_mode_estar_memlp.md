---
status: "resolved"
date: "2026-08-14"
main_address: "Goal058.G3.ActualModeEStarCarrier"
related_addresses: ["Goal058.G3", "Goal058.G3.ActualModeRegularPacket"]
ancestor_addresses: ["Goal058.G3.ActualModeSource"]
child_or_next_addresses: ["Goal058.G3.ActualModeExistence", "Goal058.G3.Lemma72Rate"]
raw_address_notation: "Goal058.G3.ActualModeEStarCarrier"
normalized_addresses: ["Goal058.G3.ActualModeEStarCarrier", "Goal058.G3", "Goal058.G3.ActualModeRegularPacket", "Goal058.G3.ActualModeSource", "Goal058.G3.ActualModeExistence", "Goal058.G3.Lemma72Rate"]
address_status: "resolved_local_consequence"
blocker: "Derive the production E_star MemLp certificate from compact support and actual-mode regularity"
collections: ["q3_docs", "math_papers"]
tags: ["Goal058", "G3", "E_star", "MemLp", "finite support"]
insight_links: []
request_nodes: ["docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md"]
strong_terms: ["WindowFiniteSupport", "sourcePositiveIndexFinset", "prolateCombination_E_star_memLp_of_actualModes"]
empty_terms: ["ready production E_star MemLp supplier"]
false_friend_terms: ["time-side L2 nonzero implies sampled E_star nonzero"]
opens_new_branch_terms: []
neighbor_addresses: ["Goal058.G3.ActualModeRegularPacket", "Goal058.G3.Lemma72Rate"]
---

# Goal058.G3.ActualModeEStarCarrier — finite-window `E_star` carrier

## Точный блокер

`ProlateKTrialSourceData.eStar_memLp` was still stored as an input even after
actual-mode regularity and exact unit time-side `L2` mass had been proved.
The question was whether the current tree already turned compact support at
`lambda_m = sqrt(m)` into the required windowed `MemLp` theorem.

## Knowledge preflight

```text
./ask.sh --deep "Goal058 E_star MemLp compact support source window finite sum lambda sqrt m prolateCombination"
```

The search found the exact local `WindowFiniteSupport` crosswalk and no ready
`MemLp` supplier.  No external source was required because this is carrier
plumbing forced by the production definitions.

## Resolved capability

For `u in [1/sqrt(m),sqrt(m)]`, an index `n > m` satisfies
`n*u > sqrt(m)`.  Compact support therefore reduces `E_star` to the fixed
finite index set `1 <= n <= m`.  Actual-mode regularity makes each summand
measurable and bounded on the window, whose `du/u` measure is finite.

The kernel-checked implementation is
`D0PstarActualProlateEStarMemLp.lean`.  It removes only the independent
`eStar_memLp` assumption once an actual pair at the D0 scale is supplied.

## Boundary and next address

Time-side unit mass does not imply that the sampled sum is nonzero; sampling
can miss support or cancel.  Thus `TrialNonzero`, positive central overlap,
the projected floor, and the coupled schedule remain downstream of the
actual indexed pair and CCM Lemma 7.2 rate.
