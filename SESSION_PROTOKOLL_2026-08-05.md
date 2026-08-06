# SESSION_PROTOKOLL 2026-08-05 — Q3 Route B: Arsenal-Integration + Memory-Contour-Architektur

Repo: Malaeu/chen_q3, Branch `rh_clean`. Session-Ende-HEAD: `af3ca317` (alles gepusht, Baum sauber).
(Session spannt 2026-08-04 → 2026-08-05; Datumsangaben absolut.)

**NACHTRAG (Session-Ende):** Zweiter Proshka-Verdict eingetroffen + materialisiert (batch-per-PHASE,
goal-close-Auto-Call KILLED, P9 CODEX_CONTROL, EXECUTOR_ARSENAL_ADDENDUM superseded, BEHAVIOR_CONTROL_
SYMMETRY) → `docs/routeB_bus/proshka/PROSHKA_VERDICT_BEHAVIOR_CONTROL_CONTOUR_2026-08-05.md` (3a12607f).
Mythos-Maps + Protokoll (3a98b715), Owner→Codex(Mac)-Handoff `docs/CODEX_HOME_HANDOFF_2026-08-05.md`
(cf828709), zwei Owner-Transkripte (af3ca317) gepusht. **Nächster Zug ist bei Codex (Mac) zuhause:
Task 1 = 5 Mac-only GAPS aus Fakt füllen, dann Task 2 = P9. Kein P9-Start durch mich (owner-relay-gated).**

## Kontext
Q3 Riemann-Hypothese Lean-Formalisierung, Route B (CHALLENGER / NOT_RH). Kanäle: Codex (Executor, Mac +
Linux = eine Rolle, zwei Körper), Fable/Mythos (Dispatcher, browser, READ-only GitHub), Proshka (Judge,
browser, READ-only GitHub), Claude Code (ich, Linux-Executor-Körper). Bus = `docs/routeB_bus/` (Goals/
Answers/Verdicts, canon+mirror).

## Ausgangslage (was war)
- Goal 051 (M1: PosDef-self-adjoint ⇒ real spectrum) als H2b-Keystone offen; Proshka hatte math kill-pass gegeben.
- Müntz-Supplier-Front unklar (angeblich 2/4).
- Kein Arsenal (K9-Kartei) materialisiert; Fable-Kernel lebte NUR im UI (keine Repo-Kopie).
- Verdacht des Owners: nach jedem Linien-Wechsel (Jan/Apr/Juni) verwaisen Konturen; Memory fragmentiert.

## Aufgabe (was zu tun war)
1. Goal-051-M1-Kontur bauen, Proshka verifizieren lassen, Codex materialisieren.
2. P-vs-NP-Lernprojekt anlegen (Erklärungen „auf Fingern").
3. Arsenal-Integration (12 Karten + Kernel v3) in die Pipeline, thin-UI/fat-repo für alle Kanäle.
4. Volle System-Zensur (alle Zyklen/Datenbanken/Regeln) → SYSTEM_SPEC; Memory-Contour vereinheitlichen.
5. Codex-internen Zyklus rekonstruieren (auch die Nicht-GitHub-Teile).
6. Budget-kritisch: Proshka effizient nutzen (batch-per-PHASE, ein lebender Chat).

## Erledigt
- **Goal 051 (M1):** Kontur v1/v2 gebaut (Mythos-Audit: M0-Layer + „H2-Zweig nicht ganze RH"), Proshka math
  kill-pass materialisiert (Konvention `Q*D=Dᴴ*Q`, CFC.sqrt, charpoly_units_conj); Codex autorisiert.
  Übernacht hat Codex M1 (`posDefSelfAdjoint_exists_hermitian`) + M0/M2/M3-Bausteine sorry-frei bewiesen (21 neue Lean-Files).
- **Müntz-Korrektur:** Front ist **4/4 DONE** (hRm commit d3ca3c9e, habs Goal 052 79d80630, [MacOS]), NICHT 2/4;
  `lake build` bestätigt (8055 Jobs, 0 sorry, Standard-Triple); Journal + Proshka-Mirror nachgezogen.
- **P-vs-NP-Projekt:** `/mnt/hdd01/Soft/GitHub/p_vs_np/` (README + NOTES.md, 8 Abschnitte).
- **Arsenal-Integration Ф0-Ф7:** KERNEL v3 (`PROJECT_INSTRUCTIONS_v3_arsenal.md`, ERSTE Repo-Kopie),
  `ARSENAL_CARDS_v1.md` (12 Karten C01-C12), Proshka `STANDING FETCHES` + `ARSENAL_MANDATE_2026-08-04.md`,
  `EXECUTOR_ARSENAL_ADDENDUM_2026-08-04.md` (AGENTS.md + CLAUDE.md), ARSENAL-Ledger in ROUTE_B_STATE.
- **Arsenal ERSTES Live-Feuer:** Proshka-Verdict 054 nutzte **[C10]** (surrogate ccmQKernel getötet) + **[C09]** (precommit) + AUTOPSY.
- **Kanal-Erkenntnisse:** Fable liest GitHub LIVE (connector, 200+SHA bewiesen), schreibt NICHT (READ-only);
  Executor = eine Rolle in zwei Körpern (Codex Mac / Claude Code Linux); bootstrap-Muster für Fable+Proshka.
- **Memory-Audit + SYSTEM_SPEC:** 8 Ären, jeder Wechsel verwaist Kontur; Klassifikation ALIVE/OUTGROWN-archive/
  ORPHANED-rewire/BUGS. Bug behoben: **c_* = 11/10 kanonisch** (stale 1.5 in q3-CLAUDE.md:258 gefixt, Provenance).
- **Mythos-Plan-Review v2:** APPROVED_WITH_REPAIRS (12. stale Pointer, oracle-split, anti-orphan-clause,
  Reihenfolge P1a-P7, Budget-Verfeinerungen).
- **Codex-Zyklus-Rekonstruktion (3 Agenten):** Config (gpt-5.6-sol/never/chrome-devtools + 3 Sub-Agenten),
  5-Stufen-Loop, gemessene Kadenz (Fresh-chat-per-node-Antipattern bestätigt: 14 Verdicts, 276KB-Uploads,
  ~21min each), 9 Off-Git-Verhalten. → `CODEX_CYCLE_RECONSTRUCTION_2026-08-05.md`.
- **Proshka Architektur-Verdict:** unified one-Spine contour **RATIFIED** (impl open); Sensor-revive-after-rewrite,
  AUTOPSY-Schema v1 (24 Tags), Namewatch nicht-K1-allein, Bridge = wall-family-not-C13, anti-orphan als DATEN.

## Geprüft
- Müntz `lake build`: 8055 Jobs, 0 sorry/error, Standard-Axiom-Triple. Alle 21 M-Chain-Files sorry-frei.
- c_*-Drift per Grep: 11/10 ≡ 1.1 (ein Wert), einziger Ausreißer 1.5 (gefixt). NICHT auf 1.66 „getunt".
- Fable-Zugriff: HTTP 200 + SHA a13dfbe1 (live fetch = mein sha256sum = origin).
- Parallelarbeit ohne Kollision: Codex mergte unsere Arsenal-Commits selbst ([MacOS][Merge]); alle Banks intakt.

## Versendet (relayed, nicht auto)
- An Mythos: Arsenal-Aufgabe, Plan-Check (audit+spec), Codex-Sync-Phrasen.
- An Proshka: Ф3-Mandat, Architektur-Auftrag (ein Batch-Verdict). NACHGEREICHT: Chat-Modell + CODEX_CONTROL —
  **zweites Proshka-Verdict noch ausstehend**.
- KEINE Aristotle-Submission, KEINE Route-Promotion, Bus 010 VOID durchgehend.

## Offen — nächste Schritte
1. **Zweites Proshka-Verdict** (Chat-Modell batch-per-PHASE + `CODEX_CONTROL.md`-Symmetrie) abwarten → in denselben Contour mergen (P6/P9).
2. **Unified-Memory-Contour materialisieren** P1a→P9 (Proshka CODEX DIRECTIVE, OWNER_RELAY_REQUIRED, per-action-OK):
   P1a Bugs (c_* verifiziert; Zombie-Monitore PSD_STEP33/PHASE taggen; Rule-A/B-Disambiguation) →
   P1b 12 stale Pointer fixen (inkl. Spine-Karten-Pointer #12 → ARSENAL_CARDS_v1) → P6+P8 Executor-Addendum-Diff →
   P2a AUTOPSY-Schema → P2 wall-map → P4 one-Spine + Trigger-Reanchor → P5 Semantic-Index NEU bauen (Korpus existierte nie) →
   P3 namewatch als GOVERNOR-Extension + 5 Plants → P7 Meta-Corpus.
3. **Codex zuhause (Mac):** die 5 Mac-only-GAPS in CODEX_CYCLE_RECONSTRUCTION ausfüllen (Mac-config, desktop-app-stack,
   auth, standing-goal-contour, exakter chat-open/continue-Trigger).
4. **Math-Front G5/S1:** SlotS1-Supply noch nicht geschweißt (PSWF/Legendre-Konstruktor gebaut, Zusammenbau offen).
   Ф6 (Live-Arsenal-Lauf auf `𝒟_m`) vom Owner zuhause zu starten.
5. **Source-faithful bridge:** Shape-Test (4 Fronten H2a/H2b/S1/Müntz) VOR jeder C13-Prägung.

## Wichtige Fakten
- **EXECUTOR = eine Rolle, zwei Körper** (Codex Mac / Claude Code Linux); Fable+Proshka READ-only via GitHub-connector.
- **c_* = 11/10** kanonisch (exakte Rationale, Provenance A3/symbol_floor.tex; NICHT die Alpha, keine offene Konstante).
- **Proshka-Budget ~200 EUR/mo** → BATCH-PER-PHASE in EINEM lebenden Chat; Fanout verboten; Meter in STATE.
- **anti-orphan-clause:** jede neue Kontur deklariert trigger_owner + existing_gate + spine_section, sonst `ANTI_ORPHAN_DECLARATION_MISSING` — heilt die Wurzelkrankheit maschinell.
- **Kandidat-Zentralobjekt** `SOURCE-FAITHFUL IDENTIFICATION BRIDGE` (Autopsy-Konvergenz H2a/H2b/S1/Müntz) = UNTESTED, one-wall-family, C13 NICHT geprägt.
- Route bleibt CHALLENGER / NOT_RH; Bus 010 VOID; keine RH-Behauptung.

## Dateien (absolute Pfade)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/MEMORY_ARCHITECTURE_AUDIT_2026-08-05.md` (Plan P1-P8, root disease, budget law)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/SYSTEM_SPEC_2026-08-05.md` (8-Ären-Zensur, Klassifikation, BUGS, behavior-control-symmetry)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/MYTHOS_PLAN_REVIEW_MEMORY_CONTOUR_v2_2026-08-05.md` (APPROVED_WITH_REPAIRS)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/CODEX_CYCLE_RECONSTRUCTION_2026-08-05.md` (Config+Loop+Kadenz+9 off-git+Mac-GAPS)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_UNIFIED_MEMORY_CONTOUR_2026-08-05.md` (Architektur-Verdict, RATIFIED)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/docs/PROJECT_INSTRUCTIONS_v3_arsenal.md` (KERNEL v3, SHA a13dfbe1)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/docs/ARSENAL_CARDS_v1.md` (12 Karten, SHA 018dbf6b)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/EXECUTOR_ARSENAL_ADDENDUM_2026-08-04.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` (+ STANDING FETCHES; Backup ca9243ea)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/ARSENAL_MANDATE_2026-08-04.md`
- `/mnt/hdd01/Soft/GitHub/p_vs_np/NOTES.md` (P-vs-NP-Lernjournal)

---

# TEIL 2 — Abend 2026-08-05 (Fortsetzung)

Session-Ende-HEAD: `ac8e6e78` (alles gepusht, Baum sauber). Spannweite `af3ca317` → `ac8e6e78`.

## Ausgangslage (Teil 2)
Frage des Owners: „wo stehen wir mathematisch?" — daraus wurde ein Tag, der zur Hälfte Mathematik
und zur Hälfte Speicher-Infrastruktur war, weil die Mathematik zweimal an derselben Krankheit
hängenblieb: **wir wussten nicht, was wir schon besitzen.**

## Erledigt (Mathematik)
- **G6/SlotS2-Front eröffnet.** `Q3/Proofs/RouteB/S2GaugeNonvanishing.lean` — 6 Theoreme,
  `lake build` PASS (7746 Jobs), Axiome exakt `[propext, Classical.choice, Quot.sound]`, 0 sorry:
  `xiGauge` über Mathlibs `Gammaℝ`, `riemannXi = xiGauge · riemannZeta`, zentrierte Formen,
  `limit_eq_anchor` + `limit_at_zero_ne_zero`. **Ohne Aristotle** — lokal kompiliert.
- **S2-L2b-Diskriminator** exakt-symbolisch gerechnet (nicht float64): 1468 v3-Fenster,
  **1 innerer Mellin-Nullpunkt** (Exponenten (2,3,5), Zähler `(w−1)(3w−2)`, Nullstelle `w = 2/3`).
  Strukturbefund: zero-mass ⇔ `M(1)=0` **immer**, und `w=1 ⇔ z=−i/2` liegt auf dem Streifenrand,
  also stets harmlos; alle 28 zweigliedrigen Fenster sind strukturell innen-nullstellenfrei.
  Report: `docs/routeB_bus/S2_L2B_MELLIN_ZERO_SCAN_REPORT_2026-08-05.md`.
- **Proshka-Verdikt: FATAL** für die vorgeschlagene Substitution —
  `KILL_FIXED_WINDOW_MUNTZ_AS_CANONICAL_PSTAR_SURROGATE`. `Pstar` ist bereits source-locked auf
  `centeredPstarFamily D.kTrial`; der abstrakte `C`-Parameter ist **Interface-Polymorphie, kein
  Vererbungsmechanismus**. C10 + C09 Kills, C04-Warnung. Neuer minimaler Gap:
  `G6_S2_D0_SELECTED_FAMILY_MUNTZ_SAME_FAMILY_CROSSWALK`. Mythos akzeptierte ohne Contest.
  **Überlebt hat alles Generische**: die 6 Theoreme, der Scan als
  `FIXED_WINDOW_S2_NONVANISHING_OBSTRUCTION_NOT_UNIVERSAL`, PL2 als ratifizierter Falsifikator.

## Erledigt (Werkzeug + Speicher)
- **Linux kompiliert jetzt Lean.** Mathlib-Cache geholt (7727 Dateien). Pflicht auf dieser Maschine:
  `env -u LD_LIBRARY_PATH lake …` — das System-`libLLVM.so.19.1` verdeckt sonst das des Toolchains.
  In `CLAUDE.md` § Quick Commands festgeschrieben.
- **`aristotle_proofs.db` aufgefüllt**: 94→208 Docs, 1410→2232 Lemmas, **RouteB 124/124 Dateien
  (vorher 31 %)**, 926 RouteB-Lemmas → Mythos' R9 bestätigt. Die Morgen-Abfragen
  `riemannXi` / `centeredXi` / `completedRiemannZeta` gingen von 0 Treffern auf Treffer.
  Ehrliche Attribution `source='backfill'` (114) neben `'aristotle'` (92).
- **Werkzeugkarte generiert statt geschrieben**: `orchestrator/tools_census.py` → `docs/TOOLS.md`.
  22 lebende Werkzeuge (18 in **keiner** Regeldatei), 159 Einweg-Proben, 121 Journale
  (6 lebend / 19 eingefroren), 1 Waise (`orchestrator/sense.py`).
- **`knowledge.db` Welle 1**: Kill-Familie vereinigt — 38 Records aus 5 Dateien, 6 dateiübergreifende
  Aliase, 70 Evidence-Refs, Census-Drift 0, Abfrage in 41 ms. `L = Mplus*F_v` von 4 Kopien auf
  1 Record; Step33-Wall mit seinem Strategie-Zwilling verknüpft. CLI `orchestrator/kb.py`
  (search/show/list/add/census/export). Fünf Quellen mit Bannern eingefroren.
- **`spine.py` liest jetzt SQL** — zeigt endlich die Walls, die es seit L32–33 importierte, aber nie
  renderte (vorher 13 von 38 Records sichtbar).
- **`ROUTE_KILL_REGISTRY.md` wiederbelebt** — nicht durch Beschluss, sondern weil der heutige Kill
  formatgerecht hineingehörte (Route | Status | Grund | Rollback | nächster Zweig).
- **Erster Kartografen-Durchlauf** auf Mythos' Karte: 9 Aussagen bestätigt, 4 veraltet
  (die Karte entstand vor dem Proshka-Verdikt). `docs/routeB_bus/maps/2026-08-05_g6_s2_status_and_infra.{svg,md}`.

## Geprüft
- Alle 6 neuen Theoreme: Standard-Axiom-Triple, kein `sorryAx`, `lake build` grün.
- Scan-Ergebnis symbolisch verifiziert (`M(2/3)=0` exakt, kein numerisches Rauschen).
- `knowledge.db` **auf origin** gelesen: 38 Zeilen, 6 Aliase — nicht nur Datei-Existenz geprüft.
- JSON/YAML nach dem Einfrieren weiterhin parsebar; Migration reproduzierbar.
- Eigene Metriken korrigiert: `docs/TOOLS.md` fütterte sich selbst mit Referenzen (Waisen-Signal
  gelöscht); Symlink-Datierung; Atlanten ohne Datumszeilen waren unsichtbar; stilles `[:40]`-Abschneiden.

## Offen — nächste Schritte
1. **Mythos wartet auf „Release"** für (a) Papier-Kontrakt des Crosswalks (9 Proshka-Bedingungen →
   `G6·S2-XW.1…9`) und/oder (b) Spezifikation des entscheidenden Zahlentests auf einer `(m,N)`-Zelle.
2. **G2 CCM owner fork** unverändert: sieben WR-Integral-Enclosures, Daten vom Owner, Codex wartet.
3. **Kartograf als Code** — ratifiziert, heute nur von Hand ausgeführt.
4. **knowledge.db Welle 2** — Schema entworfen (`move` / `journal_entry` / `dossier` / `postmortem`
   + `link`), NICHT ausgeführt. Wichtig: `RH_TRICK_ATLAS` und `ARSENAL_CARDS` sind **keine Dubletten**.
5. **MAP.md lügt weiter absichtlich** (2 Stellen) — Abnahmetest für den Kartografen.

## Wichtige Fakten (Teil 2)
- **Interface-Polymorphie ≠ Vererbung** — der Quantor, den Codex und Mythos beide verloren hatten.
- **Lokaler Linux-Compile ist ab jetzt der Default** für kleine Lemmas; Aristotle ist Reserve.
- **Die Krankheit hat drei Projektionen**: MAP (Wahrhaftigkeit), Atlanten (Verwaisung),
  DB (Abdeckungsdrift). Ein Heilmittel: automatisches Laden am bestehenden Gate + ein Richter,
  der das Organ überführen kann.
- Route bleibt CHALLENGER / NOT_RH; Bus 010 VOID; Goal 055 held; keine RH-Behauptung.

## Dateien (Teil 2, absolute Pfade)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/S2GaugeNonvanishing.lean`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/S2_L2B_MELLIN_ZERO_SCAN_REPORT_2026-08-05.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/scripts/s2_l2b_mellin_zero_scan.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_REQUEST_G6_S2_IDENTIFICATION_2026-08-05.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/MYTHOS_BRIEF_2026-08-05_G6_S2_AND_CARTOGRAPHER.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/maps/2026-08-05_g6_s2_status_and_infra.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/aristotle_db/knowledge.db`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/aristotle_db/knowledge_schema.sql`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb_migrate_kills.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/tools_census.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/backfill_db.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/TOOLS.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/KILLS.md`
- `/home/chirurgie/.claude/plans/nea-produmaem-kak-my-glowing-whistle.md` (Plan Welle 1+2)

---

# TEIL 3 — Spätabend 2026-08-05 (Fortsetzung; Session-Ende-HEAD `d3e8ac14`)

Spannweite `ac8e6e78` → `d3e8ac14`, alle Commits 17:08–17:57 des 2026-08-05.

## Ausgangslage (Teil 3)
Nach Welle 1 stand die Frage des Owners: „wie viele Wellen waren es überhaupt, und was liegt in
den ~19 eingefrorenen Atlanten?" Daraus wurden zwei weitere Migrationswellen und — wichtiger —
die Erkenntnis, dass der Rest **nicht** pauschal Müll ist.

## Erledigt (Wissensbasis)
- **Welle 2** (`ebe86fff`): Tabellen `move` / `journal_entry` / `dossier` / `postmortem` / `link`.
  26 Moves (Atlas 11 + Arsenal 12 + TricksLibrary 3), 1784 Journaleinträge, 168 Dossiers,
  1 Postmortem. **Atlas und Arsenal NICHT verschmolzen** — die Nachfolge ist in
  `SYSTEM_SPEC` L100 deklariert, aber nie vollzogen; nur 2 von 23 Karten überlappen thematisch
  und extrahieren Verschiedenes. Verwandtschaft als 5 `same_source`-Kanten + 1 `supersedes`-Kante.
  Der verschmutzte Journal-Tag wurde in `workstream` / `state` / `channel` aufgetrennt.
- **Welle 3** (`f4a3fd12`): Proshka-Verdikte. Von 109 `PROSHKA_*.md` sind nur **61 distinkt**
  (47 Namen sind canon+mirror, 43 byte-identisch). 14 M3-Strategieblöcke + 4 strukturierte Kills
  migriert, 3 an bestehende Zeilen als Evidence gehängt. Kills 38→56, Evidence 70→176.
- **`excluded_source`** (`be0c7d24`): **113 nicht-migrierte Dateien**, jede mit der tatsächlich
  durchgeführten Prüfung und der Bedingung für ein Wiederaufgreifen. Klassen: step33 17
  (73 958 „Records", 0 Überschneidung mit lebenden Fronten), build_artifact 24, **unreviewed 33**,
  protocol 13, numeric 6, state 5, index 3, external_docs 3, literature 2, **pending_read 2**,
  config_pack 2, symlink 1, chat_export 1, already_evidence 1. **35 Dateien brauchen einen
  Menschen** — `./orchestrator/kb.py excluded` benennt sie.
- **PRIME_COMB-Familie aus dem Rest gerettet** (3 Dateien, eingefroren 2026-06-12): daraus
  **3 stehende Wände** — Kurasov–Sarnak (der Primkamm ist beweisbar **kein** Fourier-Quasikristall,
  selbst unter RH ⇒ Crystalline-Measure/Lee-Yang-Transplantat ist per Theorem tot),
  Conrey–Li (de-Branges-Positivitätszertifikat scheitert; Alias hält die verbreitete
  Fehlzuschreibung an Sarnak fest), sowie „kein Cohn–Elkies-Dualzertifikat für Nulllage"
  (Stand der Kunst, kein Unmöglichkeitssatz) — plus 3 Dossiers.
- Endstand Basis: **2041 Records** (kill 59 · move 26 · journal 1784 · dossier 168 · postmortem 1),
  113 registrierte Ausschlüsse, `integrity ok`, Census 0 Drift.

## Erledigt (Kanäle & Aufträge)
- **Proshka-Systemprompt entzweit gefunden und geheilt** (`5d85dabf`): die Bus-Kopie war die
  **Vor-Arsenal-Version ohne `STANDING REPO FETCHES`** — sie hätte `ARSENAL_CARDS_v1.md` und das
  Mandat nie geholt. Geprüft: 0 Zeilen nur in der alten Fassung, die neue ist strikte Obermenge.
  Alle drei Arbeitskopien jetzt byte-identisch (`663b3875`); der alte Text lebt nur noch als
  `_backups/PROSHKA_SYSTEM_PROMPT_v2_working_2026-08-04_pre-arsenal.md`.
  ENTRYPOINT/POLICY unterscheiden sich nur um YAML-Frontmatter — harmlos.
- **`docs/CODEX_TASK_2026-08-05_EVENING.md`** (`48d77990`): vier Aufträge für den Mac-Körper —
  (1) die fünf Mac-only GAPS füllen, (2) die Zertifikatsdaten für den G2-owner-fork erzeugen,
  (3) `knowledge.db` benutzen (mit frozen-vs-MIRROR-Liste, damit sein Loop nicht bricht),
  (4) optional den `unreviewed`-Rest lesen.
- **`docs/Codex/`** (`3eacd85e`, `a9c53c9e`): Startprompt + `README.md` mit Namenskonvention und
  der Regel *Prompt ist Zeiger, nicht Nutzlast*.

## Erledigt (Mathematik-Front, ohne Materialisierung)
- Mythos lieferte auf „го (а)" den **Papier-Kontrakt** `G6·S2-XW` (v1 → v1.1 → v1.2), der
  Proshkas neun Bedingungen 1:1 trägt. **Zwei owner-seitige Pre-flight-Prüfungen korrigierten ihn:**
  1. `XW.0` war **kein** neues Gate: `MuntzV3ProlateCombinationReceiver.lean:49` beweist die
     Müntz-Identität für `prolateCombination` über die v3-Klasse bereits sorry-frei; Nullmasse auf
     der positiven Halbachse und Lipschitz der Kombination liegen ebenfalls vor. Beide Dateien
     fehlen in Proshkas MANDATORY_INPUTS.
  2. `Λ = P.pw.lambda` ist **kein Fakt, sondern ein freies Feld**. `ProlateOperatorData` hält
     `lambda : ℝ` frei; `ProlatePair` sagt selbst: „All analytic facts are fields (hypotheses),
     not existence theorems". Eine Bindung an `λ_m = √m` existiert **nirgends** im Baum.
     Mythos' AUTOPSY: dieselbe Interface-Polymorphie-Klasse, die Proshka bei PL2 getötet hat.
- Daraus v1.2 mit `XW.0a` (konkreter Modenkonstruktor) / `XW.0b` (Lipschitz mit expliziter
  m-Abhängigkeit) und `XW.5` als **fehlende Instantiierung** statt Einzeiler-Check.
- **Maßstab von `XW.0a` gemessen:** Mathlib enthält **null** `prolate`/`spheroidal` und
  **null** Sturm–Liouville-Dateien; nur der generische Hilbertraum-Rahmen existiert.
  `prolateWaveExpression` ist der singuläre Sturm–Liouville-Ausdruck. `XW.0a` bedeutet also
  Spektraltheorie eines singulären ODE von null an — keine Objektkonstruktion in bestehender Theorie.
- **Zweite Proshka-Anfrage gestellt** (`d3e8ac14`, gebatcht wie von ihr verlangt): ist der
  PSWF-Konstruktor für source-faithfulness zwingend, oder genügen source-locked Moden mit
  zertifizierten Schranken? Und: läuft `XW.8` (Provenienz, ihr stärkstes Gate, Audit **bestehender**
  Objekte) **vor** `XW.0a`, damit ein Provenienz-Kill die ganze PSWF-Programmatik erspart?

## Geprüft
- `knowledge.db` **auf origin** gelesen (nicht nur Dateiexistenz): `integrity ok`, 2041 Records.
- Migrationen nach dem Einfrieren reproduzierbar; JSON/YAML weiterhin parsebar.
- Eigene Fehler gefunden und behoben: FTS5-Falle (`DELETE` auf external-content ⇒
  „disk image is malformed"; korrekt ist `INSERT INTO x_fts(x_fts) VALUES('delete-all')`),
  `Müntz`→`M_NTZ` in IDs (Diakritika-Faltung), Census zählte nur die kill-Schicht,
  stilles `[:40]`-Abschneiden im Ledger-Report.
- Audit-Korrekturen von Hand: `TRICKS_LIBRARY` hat 3 Records (nicht 2), `docs/insights` 165
  Dateien (nicht 194), Verdikte 61 distinkt (nicht 109).

## Versendet (relayed, nicht auto)
- An Mythos: „го (а)", danach zwei Korrekturen (Receiver existiert; fields-vs-theorems) und die
  Mathlib-Messung mit Vorschlag `XW.8` vor `XW.0a`.
- An Proshka: zweite Adjudikationsanfrage (Link auf `d3e8ac14`).
- An Codex: noch **nichts** — der Startprompt liegt bereit in `docs/Codex/`.

## NACHTRAG beim Protokollschluss — Codex hat über Nacht P9 vollzogen

Beim letzten `git pull --rebase` kamen drei Mac-Commits herein, entstanden **während** dieser
Session (2026-08-06, 00:34 / 01:09 / 06:57). Der Mac-Körper hat eigenständig gearbeitet:

- **`7e319bdc` „Implement unified memory control spine"** — P9 materialisiert:
  `docs/CODEX_CONTROL.md` (509 Zeilen, EIN Verhaltens-Kern für beide Körper) neu;
  `CLAUDE.md` von 541 Zeilen auf einen **dünnen Zeiger** reduziert, ebenso `AGENTS.md`,
  `README_SETUP.md`, `codex_prompts/`. Dazu `orchestrator/AUTOPSY_SCHEMA.md`,
  `BEHAVIOR_CONTROL_REGISTRY.json`, `ARTIFACT_IDENTITY_REGISTRY.json`,
  `docs/P1_POINTER_CENSUS_2026-08-05.md`,
  `docs/…MEMORY_CONTOUR_IMPLEMENTATION_REPORT_2026-08-06.md`.
- **Die fünf Mac-only GAPS sind GEFÜLLT** (`CODEX_CYCLE_RECONSTRUCTION` §5, jetzt „resolved from
  the primary Mac body"): `gpt-5.6-sol` / effort `xhigh`, `sandbox_mode = danger-full-access`,
  `approval_policy = never`, native `notify` über den Sky-Computer-Use-Client (der Pfad, den der
  Linux-Slice nicht hat), `chrome-devtools` auf `127.0.0.1:9222` **zusätzlich** zum eingebetteten
  authentifizierten Browser (das eine hat das andere nicht ersetzt), Plugin-/Connector-Liste,
  Ghostty für Repo-Pfade. Damit kodifiziert P9 Fakten statt unserer Vermutungen.
- **Er hat unsere heutige Arbeit gelesen und integriert:** `CODEX_CONTROL.md` nennt
  `knowledge.db` / `kb.py` viermal; unsere Frozen-Banner in `Q3_OBSTRUCTION_ATLAS.md`,
  `S5_FAILURE_ATLAS.md` und `RH_TRICK_ATLAS.md` hat er zu
  `STATUS: SNAPSHOT_FROZEN (source cutoff …; migrated …)` präzisiert.
- Zusätzlich `c9669b94` (dependency-aware generated scan) und `1efda3f8`
  (Sensors: snapshot + PrimeCert route kill).

**Damit sind Punkt 3 der Offen-Liste (GAPS) und die P9-Materialisierung erledigt — nicht von uns.**
Beide Konturen sind zusammengelaufen: er schreibt in dieselbe Basis-Disziplin, die hier heute
gebaut wurde. Der Sitzungsschluss ist deshalb ein Übergabepunkt, kein Stillstand.

## Offen — nächste Schritte
1. **Proshka-Antwort** auf die Konstruktor-Frage abwarten; danach entscheidet sich, ob G6 ein
   Mehrmonats-Formalisierungsprogramm ist oder ein Zertifikatspfad.
2. **Kontrakt v1.2 materialisieren** — erst nach ihrer Antwort (Q3 prüft die Dekomposition).
3. ~~Codex: fünf GAPS~~ → **ERLEDIGT über Nacht** (siehe Nachtrag). Offen bleibt aus
   `docs/CODEX_TASK_2026-08-05_EVENING.md` nur Task 2 (G2-Zertifikatsdaten) und Task 4 (optional).
4. **G2 owner fork** unverändert: sieben WR-Integral-Enclosures, Daten vom Owner.
5. **35 Dateien brauchen einen Menschen** (`kb.py excluded`): 33 `unreviewed`, 2 `pending_read`.
6. Kartograf als Code weiterhin offen; MAP.md lügt weiter absichtlich (Abnahmetest).
7. **NEU: `docs/CODEX_CONTROL.md` (509 Zeilen) ist ab sofort der kanonische Verhaltens-Kern
   auch für den Linux-Körper** — beim nächsten Sessionstart zuerst lesen; `CLAUDE.md` ist nur
   noch Zeiger. Noch nicht von uns gegengelesen.

## Wichtige Fakten (Teil 3)
- **Pre-flight hat zweimal hintereinander gerettet**, was Verdikt und Kontrakt beide übersahen.
  Beide Male 30 Sekunden `kb.py ask` + zwei greps. Das Organ arbeitet.
- **Der G6-Front ist nicht an einem Lemma hängen geblieben, sondern an einer Objektkonstruktion.**
- **Interface-Polymorphie ≠ Vererbung** — zweimal an einem Tag dieselbe Klasse Fehler
  (Proshka bei PL2, Mythos bei `λ`).
- RISIKO: `knowledge.db` ist ein 8,3-MB-Binary in git; jede Neumigration legt einen vollen Blob ab.
- Route bleibt CHALLENGER / NOT_RH; Bus 010 VOID; Goal 055 held; keine RH-Behauptung.

## Dateien (Teil 3, absolute Pfade)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/aristotle_db/knowledge.db`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/aristotle_db/knowledge_schema.sql`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb_migrate_moves.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb_migrate_dossiers.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb_migrate_journal.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb_migrate_verdicts.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb_migrate_primecomb.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb_register_excluded.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/KILLS.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/CODEX_TASK_2026-08-05_EVENING.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/Codex/PROMPT_2026-08-05_evening.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/Codex/README.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_REQUEST_G6_S2_XW_CONSTRUCTOR_2026-08-05.md`
