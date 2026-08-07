# SESSION_PROTOKOLL 2026-08-07 — Q3: Werkzeug-Kontur, CCM-Brücke, Phase 0

Repo: Malaeu/chen_q3, Branch `rh_clean`. Session-Ende-HEAD siehe letzter Commit dieses Tages
(alles gepusht). **Linux-Körper war heute der Executor** — der Mac schweigt seit `7dbfb431`
(2026-08-06 23:16); null Fremd-Commits auf `origin` an diesem Tag.

## Kontext

Q3 Riemann-Hypothese, Route B = CHALLENGER / NOT_RH. `BUS_010: VOID` · `GOAL_055: HOLD` ·
`PX_RH_CLAIM: NOT_MADE`. Kanäle: Codex (Mac, heute inaktiv), Mythos (Aufklärung), Proshka
(Richter), Claude Code (Linux, heute Executor).

## Ausgangslage

Gestern: `knowledge.db` lebt, Session-Start-Ordnung vollständig auditiert,
`session_start.sh` als einziger Einstieg. Offen: Codex' Aufgaben 6–13 unberührt.

## Erledigt

### A. Mathematik — die Hauptsache des Tages

**Vergessenes Instrument gefunden.** `H2aPenaltyCoercivity.lean:395` —
`H2a_SimpleEvenGround_FromPenaltyCoercivity`, sorry-frei bewiesen: aus **einem endlichen
PSD-Zertifikat** `K − βG + τ(Gq)(Gq)* ⪰ 0` bei `a < β` folgen Existenz, **Einfachheit**,
**Geradheit** und eine **explizite Lücke `λ₂ − λ₁ ≥ β − a`**. Bei CCM ist Eingang A offen und
die Lücke `Δ_λ` in **allen sechs** zentralen Arbeiten des Clusters unbeschränkt. Die Datei war
in `MAP.md` **kein einziges Mal** erwähnt; gefunden durch eine Kartographie, die aus anderem
Anlass lief.

**Rang-eins-Lesart des Zertifikats, hier per Hand verifiziert.** `K − βG` ist absichtlich
nicht PSD — entlang der Probe gilt `a − β < 0`. Der Term `τ(Gq)(Gq)*` ist ein Rang-eins-Pflaster
genau auf diese eine Richtung: auf der Probe `q*Mq = a − β + τ`, auf dem `G`-orthogonalen
Komplement verschwindet `|q*Gy|² = 0` und übrig bleibt `y*Ky ≥ β·y*Gy`. Also ist `M ⪰ 0`
**äquivalent** zur Koerzitivität auf dem Komplement — Einfachheit, Lücke und Geradheit in einem.

**Zoom: was zum Operator trägt, ist nicht die Lücke, sondern das Zertifikat.** Galerkin liefert
nach Courant–Fischer nur obere Schranken `λ_k^{(N)} ↓ λ_k`; eine untere Schranke für `λ₂` gibt
es nicht. Das Zertifikat ist dagegen eine **Formungleichung**, und Formungleichungen übertragen
sich per Dichtheit. Auf `⟨Gq,v⟩ = 0` (Kodimension eins) folgt `λ₂ ≥ β` per min-max, mit
`λ₁ ≤ a` also `λ₂ − λ₁ ≥ β − a` **für den Operator**. Bedingung ist damit nicht «die
Sektionslücke kollabiert nicht», sondern **`β` hängt nicht von `N` ab**.

**Proshka hat Move 1 ratifiziert** (`RUN_CCM_PENALTY_CROSSWALK_BETA_DELTA_PROFILE`) mit
Pflicht-Phase-0 und **ohne** `SIEG_of_penalty` abzuwarten. Sie hat unabhängig aus der
Primärquelle bestätigt: `G = I`, `κ` und `λ² = m`, `J` kommutiert mit `K`, «even-simple».

**Phase 0 zu sieben Achteln geschlossen** (Journal: `docs/routeB_bus/PHASE0_RESULTS_2026-08-07.md`):
`λ² = m` und `L = log m` **hergeleitet**, nicht gefittet; Polblock durch **zwei unabhängige
geschlossene Formen** (`10⁻³¹`); `K` symmetrisch; `JK = KJ` exakt null; **Primblock gegen einen
externen Referenzwert auf 17 Stellen** bestätigt. Der archimedische Block läuft noch.

### B. Werkzeug-Kontur — gegen dreimaliges Vergessen an zwei Tagen

Dreimal in zwei Tagen dasselbe Muster: das Instrument existierte, das Wissen lag darin,
niemand schaute nach. Nicht Vergesslichkeit — sechs Speicher mit sechs Befehlen.

- **`./ask.sh <Begriff>`** — ein Eingang über alle sechs Speicher; druckt `НЕ НАЙДЕНО НИГДЕ`
  mit der Liste des Geprüften und Exit 1, wenn es wirklich nirgends ist.
- **`SessionStart`-Hook `q3-toolbelt.sh`** (0,1 s) — legt den Werkzeuggürtel **ohne Handlung**
  in den Kontext; warnt vor Monitoren, die über ihren Status lügen.
- **`./paper.sh <arxiv|doi>`** — PDF + Metadaten + `references.bib` + **Zotero-Item mit
  angehängter Datei** + Registerzeile. Schreibt die **Karte bewusst nicht** — die ist ein
  Urteil; stattdessen Status `NEEDS_CARDS`, sichtbar im Gürtel bis ein Mensch ihn schließt.
- **`unicode-guard.py`** protokolliert jetzt: `~/.claude/logs/unicode-guard.jsonl`.
- Kopien der Hooks liegen in `specs_docs/hooks/` mit Installationsanleitung für den Mac.

### C. Literatur — selbst geholt, nicht delegiert

Groskin `2607.02828` (Karten geschrieben; **nicht** unsere fehlende Hälfte — sein `T` ist der
archimedische Cutoff, unsere Hälfte ist `N → ∞`) und Andrews' unabhängige Reproduktion
(`10.5281/zenodo.20427500`): dessen `H_λ` und `V_n` sind **wörtlich unsere** `H_m` und `V_n_m`,
Geradheit empirisch bis `λ² = 1200` bestätigt, τ-Matrizen in öffentlichen Caches abrufbar.

### D. Regeln, die heute entstanden sind

1. **Alles Auffällige wird sofort notiert**, mit beiden Lesarten und dem unterscheidenden
   Ausgang — nicht nach dem Lauf.
2. **Ein gefundener Bug wird zuerst repariert**, vor Rückkehr zur Mathematik.
3. **Phase, dann Batch** — Fragen sammeln sich in `PROSHKA_QUEUE.md` bis zwei bis vier
   blockierende beisammen sind; Proshka denkt 20+ Minuten pro Batch.
4. **Behauptungen über Primärquellen werden geprüft**; was sich hier nicht verifizieren lässt,
   geht als `relay, nicht verifiziert` ins Artefakt und **nie** als Prämisse eines Schlusses.

## Geprüft

- `ask.sh` in beide Richtungen (findet Groskin; meldet ehrlich `НЕ НАЙДЕНО` für McDermott).
- Hook schweigt außerhalb von Q3; `unicode-guard` feuert auf gepflanzte Tag-Block-Anweisung.
- `paper.sh` End-to-End inkl. Zotero-Upload; md5 der angehängten Datei stimmt mit der Platte.
- Groskins Verifier auf dieser Maschine reproduziert: drei Routen konvergieren.
- Kein Force-Push: `7e319bdc` ist Vorfahr von HEAD (78 Commits dazwischen).

## Offen — nächste Schritte

1. **Archimedischer Block zu Ende rechnen** — Skripte und Teilergebnis liegen in
   `docs/routeB_bus/phase0_scripts/` mit READMEs. Zuerst Diagonale auf Analytik umstellen.
2. **Falls die Summe um eine Größenordnung abweicht:** nicht die Genauigkeit reparieren,
   sondern die **Brücke** zwischen ihrem Weg (Testfunktion, `1/π`) und unserem (Matrix,
   `1/π²`) herleiten — das einzige unverifizierte Glied.
3. **Codex' Aufgaben 6–16** in `docs/Codex/TASK_2026-08-06_07.md` — Blöcke I–IV, nichts davon
   angefasst. 6–8 sind dringend (drei Prüfungen, die aktiv lügen).
4. **`PROSHKA_QUEUE.md`** steht bei drei Fragen; Q1/Q3 gehören eher zu Mythos bzw. brauchen
   eine DOI, Q2 präzisiert sich erst nach Phase 1.
5. **Mythos:** M5–M8 offen; McDermott ist unbestätigt und braucht eine Quelle, sonst streichen.

## Wichtige Fakten

- Bei `m = 13` heben sich die drei Blöcke (`prime −2.94`, `pole +5.87`, `arch −2.90`) zu
  `0.0275` auf — **zwei Größenordnungen Auslöschung auf der Diagonale**. Float64 ist für ein
  Zertifikat prinzipiell untauglich; das Museumsschicht-LDL mit **exakt rationalen** Identitäten
  ist hier kein Luxus.
- **Ein grünes Move-1-Ergebnis bewiese einen Satz über die endliche CCM-Trunkierung** — und
  weder `SlotH2a` noch Eingang A für alle `λ` noch eine Operatorlücke noch RH.
- **Ein rotes Ergebnis widerlegt nichts:** die Penalty-Bedingung ist hinreichend, nicht notwendig.
- Zwei meiner Formulierungen wurden von Proshka widerlegt: `δ_N(ξ)=1` ist **keine**
  `L²`-Normierung, sondern ein linearer Anker; und `e^{−4πλ²}` ist die Rate des **prolaten
  Defizits**, nicht des Eingang-B-Zählers. Beide stammten aus Relay, das ich als Prämisse benutzte.

## Dateien (absolute Pfade)

Neu heute:
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/ask.sh`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/paper.sh`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/CHAT_DIGESTS.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/PROSHKA_QUEUE.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/PACKET_2026-08-07_INSTRUMENT_AND_GAP.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/PHASE0_RESULTS_2026-08-07.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase0_scripts/`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/maps/ROUTEB_FORK_2026-08-07_THE_GAP.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/maps/ZOOM_2026-08-07_GAP_TRANSFER_THROUGH_GALERKIN.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/maps/RECON_2026-08-07_CCM_ORIGINAL.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/proshka/PROSHKA_VERDICT_CCM_PENALTY_CROSSWALK_2026-08-07.md`
- `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/specs_docs/hooks/`
- Karten: `docs/routeB_bus/litreview/{GROSKIN_TAILORDER,ANDREWS_CCM_REPRO}_USAGE_CARDS.md`

Geändert: `MAP.md` (250 → 463 Zeilen, neu kartographiert), `CLAUDE.md` (vier Regeln),
`docs/Codex/TASK_2026-08-06_07.md` (Blöcke III–IV), `orchestrator/kb.py`,
`orchestrator/kb_migrate_verdicts.py`, `knowledge.db` (71 Zeilen).

Vortag: `/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/SESSION_PROTOKOLL_2026-08-06.md`
