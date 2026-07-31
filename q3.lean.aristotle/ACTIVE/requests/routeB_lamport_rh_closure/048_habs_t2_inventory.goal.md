# Goal 048 — habs supplier PHASE 0: 012-T2 import-closure inventory (fork A|B)

ISSUED: 2026-07-31, Mythos (habs three-move plan; transcribed by conductor-CLI on
  owner's order; source-lock verified). READ-ONLY inventory goal — runs parallel
  to anything; no Lean files created or modified in this goal.
MODE: LOCAL_FIRST · NO_ARISTOTLE · SCOPE: ABSTRACT · VERIFIER TARGET: LEAN(read)
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID · no promotion · frozen untouched

## Source (locked)

Q3 project: q3.lean.aristotle/Q3/Proofs/RouteB/EStarWindowedMellinCrosswalk.lean:573

```lean
theorem windowedMellin_E_star_zeroMass_decomposition_abs
```

proves the habs-shaped identity M(window·E*h) = ζ(s+1/2)·M(h)(s+1/2) − R⁻ − R⁺
on Re s > 1/2 (standard triple; per the 012 post-audit note the mass hypothesis is
NOT used in the absolute region). Its technical hypotheses (EStarMellinAbsolute,
MellinConvergent) are recorded at 012.answer lines 66–79.

## Task (PHASE 0 only)

1. Build the full transitive import-closure of the theorem above inside the Q3
   project (module list, file count, total LOC).
2. Determine whether the closure pulls Q3.Main or any axiom-bearing module
   (Weil_criterion / PrimeCert / prime_term_le_at_t_critical_axiom families).
3. Byte-compare the Estar and Mellin definitions used by 012 against the v3
   RequestProject definitions (precedent: R6 came out byte-identical).
4. List the exact technical-hypothesis obligations (EStarMellinAbsolute,
   MellinConvergent and anything else the theorem takes) and map each to its
   candidate discharge: E*-bound near zero (EstarBoundedBySqrtOfZeroMass_
   IccZero_IcoLipschitz, Proshka queue) / T1 tail vanishing (u > b) / other
   (name it).
5. Verdict: exactly one of

```text
HABS_EXPORT_VIABLE      (closure small, no Q3.Main/axiom modules; branch A =
                         044-template export + Ioo-indicator bridge)
HABS_REPROVE_NATIVE     (closure heavy or axiom-tainted; branch B = native v3
                         reproof ~200 lines, finite-window u=v/n + Fubini)
```

Branch EXECUTION is NOT part of this goal — a separate goal (049) will be issued
on the verdict.

## Forbidden

Creating/modifying any Lean file; touching frozen files; Aristotle; promotion;
executing branch A or B.

## Registered predictions (Mythos, before execution)

P048-1: Estar/Mellin definitions byte-identical 012 ↔ v3 (R6 precedent).
P048-2: closure ≤ 12 files and does NOT pull Q3.Main ⇒ EXPORT_VIABLE.
P048-3: the only semantic bridge for branch A is the Ioo-indicator lemma
  (Gwin h Λ s = Mellin((Ioo Λ⁻¹ Λ).indicator (Estar h)) s, ≤ 15 lines).
P048-4: technical hypotheses reduce to E*-bound + T1; no new analytic inputs.

## Answer requirements

048_habs_t2_inventory.answer.md with MYTHOS_PROSHKA_HANDOFF + ACTIONS LOG;
closure listing (modules + LOC + axiom scan result); definition byte-diff
verdicts; hypothesis-to-discharge map; ONE verdict code; scoring P048-1..4;
goal consumed by SHA-256; one non-promoting state row; ROUTE_B_STATE last;
canon+mirror one transaction.
