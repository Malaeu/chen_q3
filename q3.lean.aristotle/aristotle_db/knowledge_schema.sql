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
