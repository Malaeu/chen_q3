-- knowledge.db — one home for "have we already tried / killed this?"
--
-- Why this exists (2026-08-05): the same knowledge was scattered over five files with
-- incompatible vocabularies, and the same object (`L = Mplus * F_v`) was recorded four
-- separate times without any key linking the copies. Nothing could answer "did we already
-- kill this?" in less than an archaeological dig.
--
-- Design decision: ONE `kill` table with a `unit_type` column, not three tables. The five
-- source files differ in which optional columns they populate, not in what entity they
-- describe — and three of the four known overlaps are the SAME incident seen from a
-- different angle (dead object vs dead move vs dead route). Separate tables would force a
-- join on every real question.
--
-- Deliberately NOT here: TAINT_GRAPH and SORRY_FRONTIER. Those are regenerable build state
-- keyed on file path, with no reason, rollback or replacement semantics.

CREATE TABLE IF NOT EXISTS kill (
    id                    TEXT PRIMARY KEY,  -- machine id where one exists, else a slug
    unit_type             TEXT NOT NULL,     -- route | object | strategy | wall | criterion
    subject               TEXT NOT NULL,     -- the dead thing: route shape, candidate, move, wall
    status                TEXT NOT NULL,     -- killed | live | repaired | superseded | standing
    reason                TEXT,              -- why it died / why the wall stands
    scope_negation        TEXT,              -- what this kill does NOT kill (anti-overreach)
    rollback_target       TEXT,              -- where to fall back to
    replacement           TEXT,              -- next branch / replacement / next action
    forbidden_future_move TEXT,              -- the standing prohibition this leaves behind
    stop_code             TEXT,              -- machine failure/stop code
    track                 TEXT,              -- H-bridge | PSD-pd | RouteB | TrackB | Step32/33
    recorded_at           TEXT,              -- ISO date
    source_file           TEXT NOT NULL      -- provenance: where this row was migrated from
);

-- One kill can be witnessed by several artifacts: a Lean declaration, a file, a hash,
-- a bus answer. Kept out of `kill` so a row is never rewritten to append evidence.
CREATE TABLE IF NOT EXISTS kill_evidence (
    kill_id TEXT NOT NULL,
    kind    TEXT NOT NULL,   -- lean_decl | lean_file | md | contract_sha256 | source_lines | bus
    ref     TEXT NOT NULL,
    PRIMARY KEY (kill_id, kind, ref),
    FOREIGN KEY (kill_id) REFERENCES kill(id)
);

-- The whole point of the merge: the same kill was named differently in different files.
-- Searching any alias must find the one canonical row.
CREATE TABLE IF NOT EXISTS kill_alias (
    kill_id TEXT NOT NULL,
    alias   TEXT NOT NULL,
    note    TEXT,            -- why these two names denote the same incident
    PRIMARY KEY (kill_id, alias),
    FOREIGN KEY (kill_id) REFERENCES kill(id)
);

CREATE INDEX IF NOT EXISTS idx_kill_unit_type ON kill(unit_type);
CREATE INDEX IF NOT EXISTS idx_kill_status    ON kill(status);
CREATE INDEX IF NOT EXISTS idx_kill_track     ON kill(track);
CREATE INDEX IF NOT EXISTS idx_kill_subject   ON kill(subject);
CREATE INDEX IF NOT EXISTS idx_alias_alias    ON kill_alias(alias);

-- Full-text search over the free-text fields. External-content table: the row data stays
-- in `kill`, the index only mirrors it, kept in sync by the triggers below.
CREATE VIRTUAL TABLE IF NOT EXISTS kill_fts USING fts5(
    subject, reason, replacement, forbidden_future_move, scope_negation, stop_code,
    content='kill', content_rowid='rowid'
);

CREATE TRIGGER IF NOT EXISTS kill_ai AFTER INSERT ON kill BEGIN
    INSERT INTO kill_fts(rowid, subject, reason, replacement, forbidden_future_move,
                         scope_negation, stop_code)
    VALUES (new.rowid, new.subject, new.reason, new.replacement, new.forbidden_future_move,
            new.scope_negation, new.stop_code);
END;

CREATE TRIGGER IF NOT EXISTS kill_ad AFTER DELETE ON kill BEGIN
    INSERT INTO kill_fts(kill_fts, rowid, subject, reason, replacement, forbidden_future_move,
                         scope_negation, stop_code)
    VALUES ('delete', old.rowid, old.subject, old.reason, old.replacement,
            old.forbidden_future_move, old.scope_negation, old.stop_code);
END;

CREATE TRIGGER IF NOT EXISTS kill_au AFTER UPDATE ON kill BEGIN
    INSERT INTO kill_fts(kill_fts, rowid, subject, reason, replacement, forbidden_future_move,
                         scope_negation, stop_code)
    VALUES ('delete', old.rowid, old.subject, old.reason, old.replacement,
            old.forbidden_future_move, old.scope_negation, old.stop_code);
    INSERT INTO kill_fts(rowid, subject, reason, replacement, forbidden_future_move,
                         scope_negation, stop_code)
    VALUES (new.rowid, new.subject, new.reason, new.replacement, new.forbidden_future_move,
            new.scope_negation, new.stop_code);
END;

-- Provenance of the migration itself, so `kb census` can compare file counts against rows.
CREATE TABLE IF NOT EXISTS source_ledger (
    source_file   TEXT PRIMARY KEY,
    expected_rows INTEGER NOT NULL,   -- records counted in the frozen file at migration time
    migrated_at   TEXT NOT NULL,
    note          TEXT
);

-- ============================================================================
-- WAVE 2 (2026-08-05): positive knowledge — moves, journal, dossiers, postmortems.
--
-- Split by UNIT, not by file. Critical finding of the audit: RH_TRICK_ATLAS.md and
-- ARSENAL_CARDS_v1.md look like duplicates but are not — the succession is declared in
-- SYSTEM_SPEC L100 and never executed, only 2 of 23 cards overlap thematically, and those
-- two extract DIFFERENT things from the same source (the atlas transplants the theorem, the
-- arsenal abstracts a field-free heuristic). They share one table but keep `provenance_layer`,
-- and their kinship is recorded in `link`, not by collapsing rows.
-- ============================================================================

CREATE TABLE IF NOT EXISTS move (
    id                  TEXT PRIMARY KEY,   -- C01… for arsenal, ATLAS_nn, TRICKLIB_nn
    name                TEXT NOT NULL,
    mechanism           TEXT,               -- what the move actually does
    signature           TEXT,               -- the scan key: when does this apply
    route_projection    TEXT,               -- ROUTE_B translation / RH-Q3 analogue / use-case
    transfer_invariants TEXT,               -- K3: what must survive the import, what is dropped
    dual_question       TEXT,               -- adversarial question for the reviewer
    failure_mode        TEXT,
    next_experiment     TEXT,
    status              TEXT,               -- untested|candidate|hot|applied|parked|killed
    status_evidence     TEXT,               -- goal-NNN or autopsy line
    origin_scheme       TEXT,               -- external_theorem | corpus_chapter | lean_tactic
    provenance_layer    TEXT NOT NULL,      -- atlas | arsenal | tricks_library
    source_ref          TEXT,               -- DOI/arXiv/chapter
    source_file         TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS journal_entry (
    id            TEXT PRIMARY KEY,
    date          TEXT,
    kind          TEXT,          -- insight|synthesis|result|in_progress|final|decision|…
    title         TEXT,
    -- The source file crams workstream, status and channel into ONE parenthesised tag.
    -- Split here or the column stays unqueryable.
    workstream    TEXT,          -- Step33A.1-A | Track B B2b | Route B Lamport | …
    state         TEXT,          -- checked | in progress | OK | blocker | closed node
    channel       TEXT,          -- lean | generator | control-plane | diagnostic
    target        TEXT,
    validation    TEXT,          -- build job counts, q3_check, axiom triple
    artifact_sha  TEXT,
    boundary      TEXT,          -- the explicit non-claim — the most valuable line of an entry
    next_target   TEXT,
    body          TEXT,
    source_file   TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS dossier (
    slug         TEXT PRIMARY KEY,
    title        TEXT,
    date         TEXT,
    status_token TEXT,           -- free-text status line, e.g. validated_import_plan_not_proof
    verdict      TEXT,
    subtype      TEXT,           -- dossier | playbook | reference | template
    tags         TEXT,           -- from the KB frontmatter where it existed
    priority     TEXT,
    body_md      TEXT,
    source_file  TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS postmortem (
    id             TEXT PRIMARY KEY,
    date           TEXT,
    context        TEXT,         -- PR / file / task
    found_by       TEXT,
    what_happened  TEXT,
    root_cause     TEXT,
    rule           TEXT,         -- the preventive rule this leaves behind
    checklist      TEXT,
    correct_path   TEXT,
    source_file    TEXT NOT NULL
);

-- The cross-cutting edge table. This is what makes the merge worth doing: it records the
-- arsenal→atlas succession that no file encodes, pairs C01 with atlas card 1 WITHOUT
-- destroying either extraction, and replaces the 195 fragile string paths inside INSIGHTS.md.
CREATE TABLE IF NOT EXISTS link (
    from_type TEXT NOT NULL,     -- kill | move | journal_entry | dossier | postmortem
    from_id   TEXT NOT NULL,
    to_type   TEXT NOT NULL,
    to_id     TEXT NOT NULL,
    relation  TEXT NOT NULL,     -- cites|supersedes|same_source|applies_move|autopsy_of
    note      TEXT,
    PRIMARY KEY (from_type, from_id, to_type, to_id, relation)
);

CREATE INDEX IF NOT EXISTS idx_move_status      ON move(status);
CREATE INDEX IF NOT EXISTS idx_move_layer       ON move(provenance_layer);
CREATE INDEX IF NOT EXISTS idx_journal_date     ON journal_entry(date);
CREATE INDEX IF NOT EXISTS idx_journal_work     ON journal_entry(workstream);
CREATE INDEX IF NOT EXISTS idx_journal_state    ON journal_entry(state);
CREATE INDEX IF NOT EXISTS idx_dossier_subtype  ON dossier(subtype);
CREATE INDEX IF NOT EXISTS idx_link_to          ON link(to_type, to_id);

CREATE VIRTUAL TABLE IF NOT EXISTS move_fts USING fts5(
    name, mechanism, signature, route_projection, failure_mode,
    content='move', content_rowid='rowid');
CREATE VIRTUAL TABLE IF NOT EXISTS journal_fts USING fts5(
    title, body, target, boundary,
    content='journal_entry', content_rowid='rowid');
CREATE VIRTUAL TABLE IF NOT EXISTS dossier_fts USING fts5(
    title, status_token, verdict, body_md,
    content='dossier', content_rowid='rowid');
