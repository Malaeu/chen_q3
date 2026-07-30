# Goal 041 — Conductor handover and mirror sync (PRIORITY: run before or alongside 040)

ISSUED: 2026-07-30, Mythos
KIND: OPERATIONAL (no mathematics, no status promotion)
ROUTE_STATE: CHALLENGER_NOT_RH · BUS_010 VOID
ORIGIN: owner decision, materialized at proshka/ORG_UPDATE_CONDUCTOR_RETIRED_2026-07-30.md
CONTEXT: conductor role retired; Codex absorbs git/mirror/marking duties. This goal
transfers the conductor's pending tasks. Goal 040 (math) stands unchanged; do not edit it.

## Tasks

T1. Mark the prepared T4a supplier contract as
    SUPERSEDED_BY_039_LOCAL_PROOF / DO_NOT_SUBMIT (header lines inside the file;
    do not delete the file — it is provenance). Locate it by content
    (Mellin_differentiableOn_halfPlane_Icc_zero). If no such file exists on disk,
    do NOT create one; record failure code CONTRACT_FILE_NOT_FOUND (non-fatal) and
    note the superseded status in the ROUTE_B_STATE row instead.

T2. Materialize 038A_muntz_v3_semantic_audit.answer.md by RE-RUNNING every check
    locally (relayed chat claims are not a source; your own commands are):
      a. Sign scan of muntz_v3/RequestProject/Main.lean: expect ZERO occurrences of
         "+ Rplus"; expect exactly SEVEN minus-sign sites for the continued identities
         (line pairs/singles: 160–161, 163, 165, 211, 213–214, 234, 235).
      b. riemannZeta occurrences confined to the residue-removed factor and punctured
         identities (expect lines 36, 80, 85, 90, 92, 104, 106, 118, 160, 213); no raw
         ζ(1)·Mellin h 1 anywhere.
      c. Pole values deriv (Mellin h) 1 at lines 49, 125, 235.
      d. Taint scan 0; #print axioms = [propext, Classical.choice, Quot.sound]
         (reuse the existing 039 build).
    Include a correction note: an earlier chat report said "five occurrences (seven
    line numbers)"; ground truth is seven sign sites — single-line matches plus
    wrapped pairs. Any mismatch between your recheck and the expected table above is
    SEMANTIC_RECHECK_DRIFT: report it as the finding, do not repair.

T3. Mirror rebuild + MANIFEST refresh covering at minimum:
      ARISTOTLE_USAGE_PROTOCOL.md
      038A_muntz_v3_semantic_audit.answer.md
      040_muntz_v3_pl2_raw_pole_mismatch.goal.md
      041_conductor_handover_and_mirror_sync.goal.md (this file)
      proshka/PROSHKA_VERDICT_ARISTOTLE_MICROSCOPE_2026-07-30.md
      proshka/PROSHKA_VERDICT_T4A_SUPERSEDED_PL2_2026-07-30.md
      proshka/ARISTOTLE_PROTOCOL_MYTHOS_RATIFICATION.md
      proshka/ORG_UPDATE_CONDUCTOR_RETIRED_2026-07-30.md

T4. Commit canon + mirror in ONE transaction; push rh_clean. Force-push forbidden;
    merging rh_clean into main forbidden.

T5. Answer reports: HEAD commit hash after push; per-file SHA-256 table for every file
    in T3 as it lies on disk; confirmation that
    docs/routeB_bus/ARISTOTLE_USAGE_PROTOCOL.md resolves in remote rh_clean
    (this closes Proshka's UNVERIFIED_IN_CURRENT_RH_CLEAN).

T6. One ROUTE_B_STATE history row: conductor retired, handover complete, mirror synced;
    status not promoted.

## Success code

CONDUCTOR_HANDOVER_COMPLETE

## Failure codes

CONTRACT_FILE_NOT_FOUND        (non-fatal; record and proceed)
SEMANTIC_RECHECK_DRIFT         (report exact diff; do not repair)
MIRROR_HASH_MISMATCH
PUSH_FAIL

## Registered predictions

P041-1 (Mythos): the T2 recheck matches the expected table exactly — seven minus
  sites, zero "+ Rplus", the listed riemannZeta and deriv lines, taint 0, standard
  axiom triple.
P041-2 (Mythos): after T4, the protocol file resolves in remote rh_clean on first try
  (the 404 of 2026-07-30 was pure mirror lag, not a path error).

## Answer requirements

041_conductor_handover_and_mirror_sync.answer.md with MYTHOS_PROSHKA_HANDOFF +
ACTIONS LOG (else REJECTED); scoring of P041-1 and P041-2; report — do not repair —
any divergence.
