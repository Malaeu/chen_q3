# Memory Architecture Audit — the June split and how to reunify (2026-08-05)

**Trigger:** owner noticed that since the ~June switch to the Route B / bus / arsenal structure,
the old knowledge banks (atlases, the decision-cycle, semantic search) stopped being updated and
consulted — "we're living on pre-switch work and losing new information."

**Verdict: confirmed by dates.** Memory did NOT get lost — it FRAGMENTED into three disconnected
eras. Raw data is alive; the *curated map* and the *decision hook* that consulted it are frozen.

---

## The three eras (last-touched dates prove it)

### ERA 1 — the old DECISION-CYCLE (dead since Jan–Apr 2026)
This is the "hook that consulted atlases on every answer + logged why-we-did-NOT-take-a-route":
- `q3.lean.aristotle/ACTIVE/pipeline/codex_agent_loop_notes.md` — **Jan 29** (the loop)
- `ACTIVE/pipeline/problem_solver_prompt.md` — **Jan 29** (the solver prompt)
- `ACTIVE/pipeline/ALTERNATIVE_PATHS.md` — **Jan 29** (route-not-taken records)
- `ACTIVE/pipeline/RESEARCH_ORACLE.md` — **Apr 12** (semantic search doctrine)
- `whyNotA` / `whyNotC` / `whyNotTaylorPayload` decision-record mechanism — lives only in Step33
  `generate_step33_*` payloads (frozen); nothing equivalent in Route B.
- Embedding index infra `scripts/refresh_q3_docs.py` — **Apr 12**; `.qmd_cache` last activity ~Jul 31.
  → `research_oracle.py query -c q3_docs` almost certainly does NOT index Route B / arsenal / recent
    verdicts. Semantic search is blind to post-April work.

### ERA 2 — the CURATED ATLASES (frozen 2026-06-12/13, the switch date)
Positive+negative curated maps — and they are STILL cited as live:
- `Q3_OBSTRUCTION_ATLAS.md` (wall map / "the dragon" / Step 32 threat model) — **Jun 12**
- `docs/RH_TRICK_ATLAS.md` (moves) — **Jun 13**
- `docs/trackB/S5_FAILURE_ATLAS.md` — **Jun 13**
- `docs/ERRORS_DESTROYER.md` — **Jan 29** (cited in CLAUDE.md "read before every PR")
- **Cited as LIVE in** `AGENTS.md` ("Root atlas: Q3_OBSTRUCTION_ATLAS.md"), `README_SETUP.md`,
  `codex_prompts/q3_step32_goal.md`. → Codex/Fable plan against a 2-month-old threat map.
- **grep proof of the broken back-loop:** post-June objects (054, Müntz v3, edge-sliver,
  IdentificationAt, arsenal, H2b, antipodal) → **0 hits** in Obstruction Atlas, 1 in Trick Atlas.
  No post-June wall or move was ever folded back into the atlases.

### ERA 3 — the NEW LIVE CONTOUR (post-June, working)
Raw knowledge IS being written — just scattered across formats:
- `q3.lean.aristotle/aristotle_db/aristotle_proofs.db` (SQLite) — **Aug 5** (Codex, per Lean commit)
- `q3.lean.aristotle/docs/INSIGHTS.md` — **Aug 5** (all channels)
- Proshka verdicts in `docs/routeB_bus/proshka/` — continuous
- `orchestrator/state/SPINE_VIEW.md` (Knowledge Spine) — **Aug 3**
- `ACTIVE/FAILED_STRATEGIES.yaml` — Jul 31 · `ACTIVE/pipeline/FAILURE_ATLAS.json` — Jul 27
- **arsenal (Aug 4):** `ARSENAL_CARDS_v1.md` (12 move-cards) + AUTOPSY discipline (K8v3)

---

## The Knowledge Spine is a HALF-built reunification (already exists!)

`orchestrator/KNOWLEDGE_SPINE.md` + `spine.py` → `SPINE_VIEW.md` (Jul 31) already aggregates via an
adapter pattern (ScientistOne §5) and injects into goal-preambles:
```
FAILURE_ATLAS.json (object-kills) ┐
FAILED_STRATEGIES.yaml (strategy) ├─ adapter → SPINE_VIEW.md → goal preambles
INSIGHTS.md (decisions)           ┘
```
**But it does NOT pull:** the ERA-2 curated atlases (Obstruction/Trick/S5), the ERA-4 arsenal cards,
or the AUTOPSY-line stream. And there is no auto-hook re-running it on every decision (the ERA-1 loop).

---

## Cross-domain CARDS + connection graph (our new, best layer — keep building)

The 12 arsenal cards (Aug 4) are the reunification's missing POSITIVE layer: cross-domain
proof-mechanisms stripped to a signature. Owner's insight (2026-08-05): the cards let us draw LINES
between named results ("curvature = repulsion = convexity" = same mountain, different slope), and the
AUTOPSY-line stream is the *name-birth protocol* (killed routes → converging autopsies → new object →
name → judge → card Cxx). Live proof: the four fronts H2a(054)/H2b(IdentificationAt)/S1(Rayleigh)/
Müntz(E*↔ξ̂) autopsies CONVERGE on one dropped object — a `SOURCE-FAITHFUL IDENTIFICATION BRIDGE`
(concrete construction IS the source functional, not surrogate/rename). Candidate central object;
UNTESTED hypothesis, to be verified not asserted.

Planned card graph (v2, cheap): per card add `WARDROBE:` (list of the mechanism's known "clothes")
and `WALL:` (cross-link to the atlas wall it pierces). Then the graph = vertices(named results),
edges(shared signatures) — one file, the literal "line between flags."

---

## REUNIFICATION PLAN — one swod, three wires (do not hand-resurrect)

Extend the Knowledge Spine into the single source of truth; wire the disconnected eras into it:

1. **Snapshot-tag the frozen atlases.** Add `STATUS: SNAPSHOT (frozen 2026-06-12)` headers to
   Obstruction/Trick/S5 atlases + fix `AGENTS.md`/`README_SETUP`/`codex_prompts` so Codex/Fable stop
   reading a stale threat map as live. (Cheapest; removes the biggest risk.)
2. **Close the K8v3 loop: AUTOPSY → live wall-map.** Point the AUTOPSY-line stream (verdicts/answers)
   into a live wall map (revive `FAILURE_ATLAS.json` or a new one) that the Spine aggregates. This is
   the wire between the name-birth generator we built (Aug 4) and the map — the loop the owner feels cut.
3. **Re-index semantic search.** Run `refresh_q3_docs` over Route B / arsenal / verdicts so
   `research_oracle -c q3_docs` sees post-April work again. Restore the "have we solved this before?" eye.

Then extend the Spine to also pull: arsenal cards (moves), the snapshot atlases (walls, read-only),
and the autopsy wall-map — so ONE SPINE_VIEW carries: object-kills + strategy-kills + insights +
walls + moves + open name-birth candidates. Optionally re-add a decision-consult step to the executor
arsenal addendum ("before choosing a route: consult SPINE_VIEW / scan cards by signature / record
why-not"), reviving ERA-1's discipline in the ERA-3 structure.

**Net effect:** decisions again check the map, why-not is logged, cards prune the option space, and
the atlas/insight banks we built work FOR us instead of freezing. Nothing is hand-resurrected — three
wires connect what already exists.

---

## THE IDEA (filtered — the owner's actual want, stripped to essence)

A **living knowledge-crystallization loop** with FOUR moving parts:
1. **CONSULT** — every nontrivial decision first checks the map (walls + moves/cards + prior why-not),
   the way the Jan decision-hook did. Prune the option space BEFORE spending effort.
2. **RECORD** — every killed route leaves an AUTOPSY line (which structure it dropped). Already law
   (K8v3). This is the raw material of new names.
3. **AUTO-DETECT (new)** — a mechanism that watches the AUTOPSY stream and RAISES A FLAG to the owner
   automatically: *"chuvak, look — a new flag/card seems to be forming here."* Trigger = the triple
   coincidence from the name-birth protocol: (a) card-scan empty, (b) no atlas wall fits by shape,
   (c) autopsy lines of ≥2 killed routes converge on ONE dropped structure. That recurring dropped
   structure = a candidate new card Cxx (status UNTESTED). Owner is notified, not left to grep.
4. **ONE GROWING LOG** — all cards + flags + autopsy-convergences collected in ONE place (the extended
   Spine), so nothing scatters. This log is itself a corpus.

**The far goal (owner's, explicit):** once the log exists as one corpus, a SEPARATE meta-project can be
run OVER it — to find generalizations, i.e. build a tiny working **Langlands-style "grammar of bridges"**
for OUR domain: which flags sit on the same mountain (shared signature), which moves are the same move
in different clothes. Not the theory of everything — a dictionary for this war, that can later be
"revived / infused" as its own project. The `WARDROBE:`/`WALL:` card-graph is the seed of this corpus.

This is exactly the century-old idea (category theory → Langlands → Grothendieck's motives): study the
ARROWS between objects, not the objects; "same music in number theory, analysis, geometry — here is the
dictionary." We build the cheap, project-scoped version. The name-birth protocol (killed routes →
converging autopsies → name → judge → card) is literally how every named flag was born (Grothendieck's
schemes = a crystallized autopsy of the Weil-conjecture failures).

---

## INTEGRATION PLAN INTO THE FULL PIPE (to be checked by Mythos, then architected by Proshka)

Builds on the 3 wires above; adds the auto-detect + meta-corpus layer. Ordered by kill-power/cost (K2).

**P1 — Snapshot the frozen banks + stop stale reads.** Tag Obstruction/Trick/S5 atlases
`SNAPSHOT (frozen 2026-06-12)`; fix `AGENTS.md`/`README_SETUP`/`codex_prompts` pointers. (Cheapest;
removes "planning against a 2-month-old map.")

**P2 — Close the K8v3 loop (AUTOPSY → live wall-map).** Route every verdict/answer AUTOPSY line into a
live wall-map file the Spine aggregates. Format per wall: `id | dropped-structure | fronts-seen-on |
candidate-card? | status`. This is the wire the owner feels cut.

**P3 — Auto-detect + flag (owner's new ask).** A cheap read-only pass (extend `spine.py` or a sibling
`namewatch.py`) that, after each Spine refresh, checks the triple-coincidence trigger and emits a
`[NEW-FLAG?]` line to SPINE_VIEW + a one-line owner notice. No auto-promotion — owner ratifies a card
Cxx. First live candidate already found by hand: `SOURCE-FAITHFUL IDENTIFICATION BRIDGE` (H2a/H2b/S1/
Müntz autopsies converge).

**P4 — One SPINE_VIEW carries everything.** Extend the adapter to pull: object-kills + strategy-kills +
insights (already) + snapshot atlases (walls, read-only) + arsenal cards (moves) + live wall-map +
name-birth candidates. Inject into goal preambles (already the mechanism).

**P5 — Re-index semantic search.** Refresh `q3_docs` over Route B / arsenal / verdicts so
`research_oracle -c q3_docs` sees post-April work; add "empty-search reported explicitly" (K7) so a
truly-empty scan is a positive signal for terra incognita, not silence.

**P6 — Decision-consult in executor discipline.** Add to `EXECUTOR_ARSENAL_ADDENDUM`: "before choosing a
route, consult SPINE_VIEW (walls+moves), scan cards by signature, record why-not." Revives ERA-1's hook
inside ERA-3's structure — one line, no new infra.

**P7 (far) — Meta-corpus / mini-Langlands.** Once the single log is stable, spin a SEPARATE project over
it: cluster flags by shared signature, draw the bridge-grammar graph, surface generalizations. This is a
downstream deliverable, not a blocker for P1–P6.

**P8 — Auto reference-list (owner's ask, 2026-08-05).** Same disease as the atlases: the litreview system
IS built but NOT wired. State: `docs/routeB_bus/litreview/{REFERENCES.md,references.bib,litreview_check.py,
zotero_pull.py}` all Aug 3; 46 PDFs; `REFERENCES.md` already maps source→lemma/gap (Chain-of-Evidence);
`litreview_check.py` validates; `zotero_pull.py` two-way Zotero sync. But grep shows it is referenced in
ZERO live discipline files (AGENTS.md/CLAUDE.md/executor addendum/Spine/Proshka) → orphaning risk. Wire it:
add a discipline rule "whenever a goal/answer/verdict CITES a publication → (a) executor or a launched
agent finds it, (b) Proshka verifies the citation (real source, right claim, per Chain-of-Evidence + the
person-name verification gate for any human name), (c) OA PDF auto-downloaded to `pdfs/`, paywalled marked
owner-fetch, (d) row auto-appended to REFERENCES.md + references.bib." Then the reference list of every
publication used in the proof is ALWAYS current — one artifact ready for the paper, and the Spine can pull
it too. Infra exists (validator, Zotero sync, source→lemma format); this is a wiring + auto-append task,
not a rebuild.

**Missing files to hand Mythos for plan-check:** this audit doc, `KNOWLEDGE_SPINE.md`, `SPINE_VIEW.md`,
`ARSENAL_CARDS_v1.md`, `EXECUTOR_ARSENAL_ADDENDUM`, the frozen atlases (Obstruction/Trick/S5), the dead
pipeline decision-cycle (`ACTIVE/pipeline/{codex_agent_loop_notes,ALTERNATIVE_PATHS,RESEARCH_ORACLE}`).
Flow: Mythos verifies the plan against these → then Proshka architects the unified memory contour.
