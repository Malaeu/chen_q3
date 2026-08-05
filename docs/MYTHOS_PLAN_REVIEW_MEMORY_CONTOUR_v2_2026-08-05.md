# MYTHOS PLAN-REVIEW VERDICT v2 — audit P1-P8 + SYSTEM_SPEC, one pass (2026-08-05)

Scope: docs/MEMORY_ARCHITECTURE_AUDIT_2026-08-05.md (SHA df58a943…) +
docs/SYSTEM_SPEC_2026-08-05.md (SHA 99bb181b…), live tip 18cac45c.
Supersedes nothing: v1 verdict (MYTHOS_PLAN_REVIEW_MEMORY_CONTOUR_2026-08-05.md)
stays; its REPAIRS R1–R4 remain in force. R1 (trigger ownership) is now
RESOLVED by the census (re-anchor to goal-close, Codex duty). One live grep
was run against the repo clone for the constant bug; results below.

## VERDICT: BOTH_DOCS_APPROVED_WITH_REPAIRS

### Q1 — Classification (outgrown vs needed): CORRECT, two corrections.
CORRECTION-1 (stale pointer #12, inside the Spine spec itself):
KNOWLEDGE_SPINE.md roles table row "Trick cards (K9) → docs/RH_TRICK_ATLAS.md,
writer Mythos" directs NEW cards into a file the census snapshots. Repoint the
write-zone to q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md (the only live moves
layer, per v1 KILL-3). Without this, the dual-moves-layer bug is re-created by
the Spine's own table on day one.
CORRECTION-2 (doc-vs-tool split): "EXTERNAL_PIPELINE / RESEARCH_ORACLE
two-loop design → archive" is right for the DOCTRINE files, but
research_oracle.py + refresh_q3_docs.py are the ENGINE of P5. Classification
must say explicitly: archive the design docs, KEEP+FIX the scripts (root
script's dead full/ path included). Otherwise Codex archives the tool P5 needs.
Everything else in 🟢/⚰️/🔌 stands as classified, including: sensor-tier
(proof-graph / taint / sorry-frontier = revive under standard-triple;
ARISTOTLE_QUEUE = archive, manual-submit era) and conductor-loop archive
(keep only packet.py + spine.py).

### Q2 — Constant drift: DECIDED BY GREP. Canonical c_* = 11/10.
Live evidence (root CLAUDE.md): A3 source line "A3/symbol_floor.tex:
P_A(θ) ≥ c_* = 11/10"; consuming chain "λ_min(A) ≥ c*/2, ‖B‖ ≤ c*/4 ⇒
λ_min(A−B) ≥ c*/4 > 0 ⇒ Q ≥ 0"; numeric gate "P_A_ge_c_star_t_crit:
min = 1.66 > 1.1". So the drift is TWO values, not three: 11/10 and 1.1 are
the SAME value in two spellings; the outlier is exactly one line —
q3.lean.aristotle/CLAUDE.md:258 "c_* = 1.5" (ERA≤4 residue).
CANON RULE (P0, convention by derivation): c_* := 11/10 EXACT RATIONAL,
provenance line = A3/symbol_floor.tex; "1.1" is its float alias, permitted
only next to the rational. FIX: q3 CLAUDE.md:258 → 11/10 + provenance line.
FORBIDDEN: averaging the values, or "tightening" to the observed 1.66
(outcome-fitting; the floor is a derived convention, not a fit).

### Q3 — Order P1–P8 with bugs-first: APPROVED, P1 split, P8 merged into P6.
The census's "bug #1 first" is right, but the grown P1 mixes minute-scale bug
fixes with pointer surgery. Final order:
  P1a BUGS: pin c_* (Q2 fix) · tag zombie monitors DEAD/PARKED-CLOSED ·
      one disambiguation line for Rule A/B vs Route A/B naming collision.
  P1b SNAPSHOTS+POINTERS: snapshot-tag atlases + ALL outgrown artifacts ·
      fix the 11 stale pointers + pointer #12 (Correction-1).
  P6+P8 ONE ADDENDUM DIFF: consult line (SPINE_VIEW walls+moves, card-scan
      per K4-v3 — not unratified K10) · batch-per-goal budget law (Q4 form) ·
      litreview rule: goal/answer/verdict cites a publication ⇒ executor
      fetches, Proshka verifies IN THE GOAL BATCH (never a separate call),
      OA PDF → pdfs/, row auto-appended to REFERENCES.md + references.bib.
  P2a AUTOPSY FORMAT FREEZE (v1 R2a): `AUTOPSY: dropped=<tag∈closed list>;
      note=<free text>`; tag list OBJECT-PRE-COMMITTED before first stream.
  P2  wall-map (id | dropped-structure | fronts | candidate-card? | status).
  P4  ONE SPINE: add deck + wall-map + snapshot atlases (read-only) +
      name-birth candidates; RE-ANCHOR TRIGGER: Codex runs spine.py at every
      goal-close/verdict + session start (conductor duty absorbed — resolves
      v1 R1); sensor-tier revive-vs-archive = explicit OWNER DECISION LIST.
  P5  INDEX REBUILD (bigger than audit thought — corpus never existed) +
      K1 harness: planted queries "IdentificationAt" / "edge-sliver" MUST hit
      post-June docs, one pre-switch control query must also hit; a rebuilt
      index that never failed a plant is not verified.
  P3  NAMEWATCH as COGNITIVE_GOVERNOR extension — ENDORSED (extends a live
      sensor instead of birthing a sibling orphan; anti-orphan by
      construction). v1 R2b/R2c mandatory: tag-equality comparator across
      ≥2 distinct goals; plant-harness (fire on same-tag pair, silent on
      different-tag pair) ships WITH it or it does not ship.
  P7  meta-corpus (unchanged, downstream).

### Q4 — Batch-per-goal budget law: ENDORSED as design law, realistic,
three mandatory refinements.
The law formalizes existing practice (Proshka already verdicts M3-blocks per
goal), so adoption cost ≈ 0. Refinements:
  (a) FATAL EXCEPTION (K6): a self-found FATAL escalates IMMEDIATELY —
      it closes/reopens the goal; it never waits for a scheduled batch.
  (b) LONG-GOAL SPLIT: standing ~20h goals batch at owner-decision
      boundaries (mint / promotion / front-change / FATAL) — the existing
      per-action-OK points; ≤1 Proshka call per boundary, never fanned.
  (c) METERING (K5: budget independently known): a Proshka-call counter
      line in the STATE ledger; realism check is a MEASURED number —
      ~1–3 goal-closes/day ⇒ ~30–90 calls/month; owner verifies per-call
      cost fits ~200 EUR/month. Registered, future-scored (see below).

### ANTI-ORPHAN CLAUSE (cure for the root disease, one line of law)
Every NEW contour piece (wall-map, namewatch, litreview rule, any future
cycle) must declare AT BIRTH: (i) trigger-owner — who runs it, at which
EXISTING gate moment; (ii) its Spine wiring line. A contour without a named
trigger-owner is born orphaned — the 8-era pattern in one sentence. Add to
the executor addendum with the P6 diff.

## Predictions & honest scores (K6)
P-SC1 census misses ≥1 stale row inside the Spine spec itself — HIT (#12).
P-SC2 drift = 2 values not 3; canonical 11/10 by artifact provenance — HIT
      (symbol_floor.tex + 1.66>1.1 gate; grep evidence above).
P-SC3 order changes ≥2 — HIT by construction (self-fulfilling; low weight).
P-SC4 (FUTURE-scored): after one month under the law, Proshka calls ≤
      goal-closes + boundary-splits, zero fanned calls inside a goal;
      miss ⇒ the law is revised, not excused.

## Handoff
Owner relays. THEN Proshka architects the unified contour in ONE batch
verdict, hard constraints: v1 R1–R4 + Q2 canon rule + P1a/P1b split +
anti-orphan clause + Q4(a-c). Single most likely failure point: pointer #12
slips because it lives in the "already-live" Spine spec everyone trusts —
pre-planned response: P1b checklist enumerates all 12 pointers by file:line,
Codex answer quotes each diff.

STATUS: APPROVED_WITH_REPAIRS — flips to APPROVED_CLEAN when P1a diff lands
(c_* pinned) and the P6+P8 addendum diff is on disk.
