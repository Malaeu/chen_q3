# OWNER STANDING ORDER — delegated ratification for D0.7e.5a source candidates

Status: `ACTIVE_OWNER_RATIFIED / NOT_RH`
Scope: ONLY ratification of WPrime/ZEO consumer-source candidates produced by
sprint item T0 (`D0_7E_5A_CONSUMER_SOURCE_CANDIDATES.md`). Nothing else.

## What the owner delegates

The owner pre-ratifies any T0 candidate that passes ALL of the mechanical
checklist below AND receives independent CONFIRMED verdicts from BOTH
verification channels. This delegates *verification*, not *definition-minting*:
candidates must be verbatim source lines; nothing is invented.

## Checklist C (mechanical, no judgment calls)

- C1: verbatim quote + exact file:line locator + sha256 of source file;
- C2: answers request questions Q1–Q3 of `D0_7E_5A_CONSUMER_SOURCE_REQUEST.md`
      (consumer name, WPrime definition BEFORE the desired inequality,
      b-argument orientation) explicitly, not by paraphrase;
- C3: Q4 domain stated or explicitly marked OPEN (allowed);
- C4: classification is DEFINITION or THEOREM (CONDITIONAL/HEURISTIC/OUTLOOK
      candidates cannot be ratified under this order);
- C5: passes firewalls: not defined by desired RHS (TAUTOLOGY), no
      bCal/bCal^(-1) aliasing, source is not Contract v2 / alpha-demand audit /
      FIT diagnostics, no H3c/H4 import into D0;
- C6: self-citation excluded (no documents authored by this pipeline).

## Verification channels (two, independent; adversarial mandate)

- V1: Прошка (breaker head; kill + repair mandate) — attack the candidate,
      default REFUTED if uncertain.
- V2: Claude-PRO (this reviewer, via repo file
      `D0_7E_5A_PRO_VERDICT.md`) — independent adversarial pass on the same
      checklist.

Semantics: CONFIRMED×2 ⇒ write
`D0_7E_5A_PROVISIONAL_RATIFICATION.md` (status
`PROVISIONALLY_RATIFIED_UNDER_STANDING_ORDER`, quoting this order's sha) and
Codex proceeds through 5a→5c on its basis. Any REFUTED ⇒ 5a stays BLOCKED;
conflict of channels ⇒ output the conflict as the finding (P5) and stop 5a only.

## Limits (non-delegable, stay with owner)

- If T0 returns `NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE`, the choice
  to mint a NEW owner definition of the consumer returns to the owner —
  that decision cannot be delegated.
- This order expires at end of the current sprint or on owner revocation.
- Everything built on a provisional ratification carries marker
  `CONDITIONAL_ON_STANDING_ORDER_2026-07-12` until the owner confirms;
  owner rejection reverts those nodes to BLOCKED (revert path mandatory).

## Owner utterance (required to activate)

```text
OWNER UTTERANCE: Ратифицирую OWNER_STANDING_ORDER_RATIFICATION_2026-07-12.md — запиши utterance и sha.
RECEIVED_AT: 2026-07-12T12:13:15+02:00
RATIFIED_ORDER_SHA256: 5bf99950fbd6fdca6f1ebae786f98098ac83a0b024e3a04f602b19a24295695b
SHA_SEMANTICS: exact pre-activation file bytes presented to the owner; the
activation record necessarily changes the containing file and therefore does
not pretend to be its own fixed-point hash.
```
NOT_RH.
