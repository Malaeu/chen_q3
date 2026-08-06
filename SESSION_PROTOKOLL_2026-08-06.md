# SESSION_PROTOKOLL 2026-08-06 — Q3: Wissensbasis-Konsolidierung + Vollaudit der Session-Start-Ordnung

Repo: Malaeu/chen_q3, Branch `rh_clean`. Session-Ende-HEAD: `02879466` (alles gepusht, Baum sauber).
17 Linux-Commits an diesem Tag. Parallel schloss Codex vom Mac aus 15+ Untergoals von Goal 056
(D0-Reihe: finite projection reconstruction, projected Mellin coordinate, full Mellin Gwin crosswalk,
residual Mellin linearity contract).

## Kontext

Q3 Riemann-Hypothese Lean-Formalisierung, Route B (CHALLENGER / NOT_RH). Kanäle: Codex (Executor,
Mac + Linux = eine Rolle, zwei Körper), Fable/Mythos (Dispatcher), Proshka (Judge), Claude Code
(Linux-Executor-Körper). Bus = `docs/routeB_bus/`. Schreibsperre: Codex schreibt, Claude liest
(`CODEX_CONTROL` §18, gestern eingeführt).

## Ausgangslage (was war)

- `knowledge.db` existierte seit 2026-08-05 mit den Wellen 1–3 (kills, moves, journal, dossiers).
- Vier Regelkategorien waren bei Codex' P9-Migration aus `CLAUDE.md` verlorengegangen (537 → 8 Zeilen);
  drei davon am Vortag wiederhergestellt, das Branching-Protokoll noch offen.
- Die Session-Start-Ordnung war nie als Ganzes geprüft worden — nur einzelne Dateien.
- Der Owner hatte zweimal an einem Tag beinahe vorhandenen Code neu gebaut (`Gammaℝ` in Mathlib,
  `riemannXi_eq_completedRiemannZeta` in `ClassicalXiInterface.lean`); beide Funde waren Zufall,
  nicht Suchergebnis.

## Aufgabe (was zu tun war)

1. Die 60 Oracle-Suchkarten in die Basis migrieren und abfragbar machen.
2. Die Konturen nummeriert spezifizieren, Synergien und Doppelungen benennen — „banal einfaches
   System, um Fehlschläge zu senken; je mehr Knoten, desto mehr geht nicht zusammen".
3. Das Werkzeug-Handbuch aus dem Kernel in `specs_docs/` auslagern, im Kernel eine Zeile lassen.
4. Einen Arbeitsauftrag für Codex (Mac) für den Abend schreiben — eine Datei, nicht verstreut.
5. Die vollständige Karte des Session-Starts erstellen: jeder Schritt einzeln geprüft.
6. Fünf Agenten mit konkreten Teilaufgaben starten, danach gemeinsam abgleichen.

## Erledigt

### Wissensbasis (Welle 4)

- **60 Oracle-Suchkarten migriert** (`kb_migrate_searches.py`) → Tabellen `search_session` (60) und
  `search_term` (321 markierte Terme über 117 Knoten). Das ist das ursprüngliche Suchgedächtnis des
  Owners: welche Wörter trugen, welche waren leer, welche waren falsche Freunde.
- **`kb.py flags`** neu: Flaggen auf der Karte — wo bereits gesucht wurde, mit welchen Wörtern,
  zu welchem Preis. `flags <Adresse|Term>` und `flags --vocab`.
- Basisstand am Tagesende: kill 60 · move 26 · journal_entry 1784 · dossier 171 ·
  search_session 60 · search_term 321 · excluded_source 113. Antwortzeit ~44 ms.

### Spezifikationen

- **`specs_docs/TOOLS_SPEC.md`** Teil II — Werkzeug-Runbook aus dem Kernel ausgelagert;
  `CODEX_CONTROL` §16.6 auf 14 Zeilen reine Pflichten reduziert plus Zeiger hierher.
- **`specs_docs/CONDITIONAL_CONTOURS.md`** — was die bedingten Konturen taten, was davon ersetzt ist.
- **`specs_docs/CONTOURS_CONSOLIDATION.md`** — jede gefundene Kontur, bewertet nach Knotenzahl.
- **`specs_docs/SESSION_START_MAP.md`** — Teil A: wörtlicher Mitschnitt, wie Codex seinen eigenen
  Start beschreibt (Linux, ausdrücklich **nicht** Mac); Teil B: Abgleich mit dem Kernel; Teil C:
  am Tagesende mit 22 Urteilen gefüllt.

### Vollaudit der Session-Start-Ordnung (fünf parallele read-only Durchgänge)

Nicht überlappende Schnitte: Schritte 1–3 · Schritt 5 · Schritte 6–8 · Aufgabenzweige ·
zusätzliche bedingte Dateien. **Keine Datei wurde dabei geändert** — die Schreibsperre liegt bei Codex.

**Wurzelbefund.** `CODEX_CONTROL` §3 delegiert an `SESSION_ENTRY.md` und prüft nie, was es delegiert:
`SESSION_ENTRY.md:16-28` weitet den einen Kernel-Schritt auf acht aus, davon sind 5–8 vier globale
Dateien, die der Kernel nicht kennt. Das Quartett geht auf **eine** Ledger-Zeile zurück
(`PROJECT_ORCHESTRATOR.md:518`, 2026-03-07), nie revidiert. Das alte `CLAUDE.md` war Konsument, nicht
Ursprung — und war bereits **vor** seiner Löschung kaputt: es verlangte, die Abschnitte
„Active Next Step" und „Closure Tracker" zu benutzen; beide existieren in der Datei nicht.

**Drei falsche Grünmeldungen**, die aktuell lügen:

| Was | Die Lüge |
|---|---|
| `routeb_status.py --check` → `CHECK: OK` | `BUS_DIR` fest verdrahtet auf einen seit 2026-07-12 eingefrorenen Ordner; meldet `active=NONE` an einem Tag, an dem 12 Untergoals geschlossen wurden. Bescheinigt nur, dass vier veraltete Dateien untereinander einig sind |
| `P9_STRICT_PASS` | `validate_p9a()` (`spine.py:1099`) läuft **unbedingt**; `--strict` fügt genau eine Prüfung plus die Quittungszeile hinzu. Empirisch belegt: ohne `--strict` byte-identische Ausgabe |
| `IMPLEMENTATION_PLAN.md:24` | Ein verify, das **nie** bestehen kann — es verlangt eine Zeichenkette, die nur in eben dieser verify-Zeile vorkommt, und zugleich die Abwesenheit einer zweiten, die dort ebenfalls steht. Seit 101 Tagen dauerhaft rot, unbemerkt |

**Eine Regel, mehrere unvereinbare Fassungen:** Stall-Schwelle ×3 · Operator-Vokabular ×2 (exakte
String-Schnittmenge **null**) · Bus-Antwortkopf ×3 · Quartett-Reihenfolge ×3, zwei davon in
derselben Datei 290 Zeilen auseinander.

**Kosten des ehrlichen Starts:** ≈ 8 MB / 200 000 Zeilen, davon weniger als ein Zehntel aktuell
(PSD-Zweig allein 4,69 MB / 143 000 Zeilen bei null Commits in 30 Tagen).

**Was bei der Aufräumaktion nicht verlorengehen darf** (lebt nur in scheinbar toten Dateien):
Monitor-Selektor + vierstufige Wahrheitsquellen-Rangfolge (`SESSION_ENTRY.md`) · die Definitionen
der acht `escape_operator`-Werte (`COGNITIVE_OPERATORS.md`) · sieben bekannte Schleifenfallen
(`COGNITIVE_GOVERNOR.md`) · die Taktik-Empirie aus sieben `weight_sum_bound`-Varianten
(`ARISTOTLE_PROMPT_GUIDELINES.md`) · die Beförderungsregel für Embedding-Notizen
(`EMBEDDING_INGEST_WORKFLOW.md`).

### Einheitlicher Einstiegspunkt

**`specs_docs/session_start.sh`** — strikt read-only. Druckt **Zustand** statt Regeln zu wiederholen
und **bricht mit Code 1 ab**, wenn Quellen einander widersprechen. Geprüft werden: Standort/Branch/
Abstand zu origin · Kanal-Runtime **mit Alter der offenen Phase** (Veraltung prüft sonst niemand) ·
Monitore „behauptet vs. letzte Änderung" · lebender Bus mit unbeantworteten Goals · Basiszähler ·
strict-Validierung.

Erster Lauf fing beide bekannten Divergenzen und **einen bisher unbemerkten Fund**:
`036_tooth_sign.goal.md` ist ein **Goal ohne Answer im lebenden Bus** — nach der eigenen Regel
ausführbar, für den Arbiter unsichtbar, weil dieser den eingefrorenen Ordner durchsucht.

Technische Notiz: die erste Fassung nutzte `git log --since` pro Monitordatei und hing >3 min an
`PSD_STEP33_MONITOR.md` (1,46 MB) — `--since` läuft die gesamte Historie ab. Ersetzt durch
`git log -1 --format=%ct`, das beim ersten Treffer stoppt.

### Korrekturen an eigenen, bereits veröffentlichten Aussagen

| Wo | Stand vorher | Richtig |
|---|---|---|
| `ENTRY_SPEC.md:18` | `SESSION_ENTRY.md` „tot seit 6 Monaten", 2026-01-29 | das ist das Datum des **Symlinks**; die reale Datei: 2026-07-10, 27 Tage alt |
| `CONDITIONAL_CONTOURS.md` §3 | Oracle-Journal „nur April" | neueste Karte 2026-08-05 (`RouteB.G5.Mode4.RegularRow`) — genau die PSWF-Karte, lebende Kontur |
| `CONDITIONAL_CONTOURS.md` §5 | Aristotle zuletzt 2026-07-30 | lief 2026-08-05 |
| `CONDITIONAL_CONTOURS.md` §6 | acht kill-Zeilen = zweiter Konsument des Vokabulars | es ist **derselbe** `FAILED_STRATEGIES.yaml`, einmal eingelesen |

### Arbeitsauftrag an Codex

`docs/Codex/TASK_2026-08-06_EVENING.md` — eine Datei pro Abend (Regel von gestern eingehalten).
Block I (vormittags geschrieben): neue Werkzeuge lernen · `SEARCH_FLAGS` in `answer.md`-Köpfen
befüllen · Operator-Vokabulare zusammenführen · `sense.py` entscheiden · `spine.py`/Sensoren
entscheiden. Block II (nach dem Audit): Aufgaben 6–11 plus Korrektur zu Aufgabe 3.
Aufgaben 6–8 als **dringend** markiert, weil sie jetzt lügen.

## Geprüft

- `session_start.sh` real ausgeführt: Exit-Code 1, zwei Divergenzen korrekt erkannt
  (PSD-Statuslüge, Route-B-Adressrückstand), `P9_STRICT_PASS` bestanden.
- `routeb_status.py --check` real ausgeführt, Ausgabe wörtlich im Audit protokolliert.
- `--strict --stdout` als schreibfrei verifiziert (Code gelesen + `git status` danach leer);
  `--refresh` schreibt und läuft **vor** der Validierung.
- `find -iname "*baton*"` → null Dateien: „site baton" ist eine Ereignisklasse, kein Artefakt.
- `grep` über alle `*.py`: **kein einziger Schreiber** für `CHANNEL_RUNTIME.json`.
- Vor dem Push geprüft, dass Codex' Mac-Commits keine gemeinsamen Dateien berühren; Rebase sauber.

## Versendet

Nichts nach außen. Alle Commits nach `origin/rh_clean` gepusht, jeweils nach ausdrücklichem
Owner-OK. Kein Claude-Branding in den Commit-Messages.

## Offen — nächste Schritte

1. **Codex am Abend**: Aufgaben 6–11 aus `TASK_2026-08-06_EVENING.md`. Reihenfolge zwingend —
   erst `BUS_DIR` umbiegen, **dann** den alten Bus archivieren, sonst meldet der Arbiter
   `BUS: closed=NONE`.
2. **Branching-Protokoll** — die vierte bei der P9-Migration verlorene Regelkategorie, noch nicht
   in die aktive Kontrolldatei zurückgeholt.
3. **`036_tooth_sign.goal.md`** — unbeantwortetes Goal im lebenden Bus; klären, ob offen oder
   stillschweigend erledigt.
4. **SEARCH_FLAGS-Sammler** — bewusst noch nicht geschrieben: erst muss das Feld befüllt sein,
   sonst entsteht ein leeres Skript und eine weitere tote Kontur.
5. **Proshkas Antwort** zur Frage, ob der PSWF-Konstruktor überhaupt nötig ist (`d3e8ac14`),
   steht weiterhin aus.
6. **Mac-Variante der Start-Ordnung** nicht erhoben — dort anderer Konfig (`sandbox_mode`, `notify`,
   eingebauter Browser). Keine Schlussfolgerung dieses Audits ohne eigene Prüfung auf Mac übertragen.
7. **`SESSION_START_AUDIT_2026-08-06.md` löschen**, sobald alle Punkte abgearbeitet sind —
   ausdrücklich als temporär markiert, Löschung nur mit Owner-Freigabe.

## Wichtige Fakten

- Route B bleibt CHALLENGER / NOT_RH. `BUS_010: VOID` · `GOAL_055: HOLD` · G2/CCM eingefroren ·
  `PX_RH_CLAIM` einziges Owner-Gate. Mathematik wurde heute vom Linux-Körper nicht bewegt.
- Von den drei Monitoren lügt genau einer: `PSD_STEP33_MONITOR` behauptet `ACTIVE` bei null Commits
  in 41 Tagen. Grund messbar: Codex' Commit `7e319bdc` stufte an diesem Tag die beiden anderen
  Monitore herab und **übersprang** PSD.
- `PHASE_MONITOR` und `PSD_STEP33_MONITOR` parken einander gegenseitig, wobei eine der beiden
  Begründungen falsch ist.
- 5 von 6 der jüngsten Commits in `PHASE_MONITOR` (geparkt) sind in Wahrheit **Route-B-Notizen**.
- Das lebende Operator-Vokabular ist Proshkas Achterset: 20 reale Werte in `docs/routeB_bus/`,
  davon `MINIMAL_LEMMA` ×14. `escape_operator:` kommt dort **null** Mal vor.
- `SPINE_VIEW.md` ist ein fremdes Artefakt: `observability.db` liegt nicht in git, die Ansicht wird
  vom Mac committet und weicht lokal in Snapshot-ID, drei Zählern und zwei nicht existierenden
  Bus-Dateien ab.

## Dateien (absolute Pfade)

Neu:
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/specs_docs/SESSION_START_AUDIT_2026-08-06.md` (temporär)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/specs_docs/session_start.sh`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/specs_docs/CONTOURS_CONSOLIDATION.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb_migrate_searches.py`

Geändert:
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/specs_docs/SESSION_START_MAP.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/specs_docs/ENTRY_SPEC.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/specs_docs/CONDITIONAL_CONTOURS.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/specs_docs/TOOLS_SPEC.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/Codex/TASK_2026-08-06_EVENING.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/CODEX_CONTROL.md` (§16.6, §17, §18)
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/orchestrator/kb.py`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/aristotle_db/knowledge.db`

Vortag:
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/SESSION_PROTOKOLL_2026-08-05.md`
