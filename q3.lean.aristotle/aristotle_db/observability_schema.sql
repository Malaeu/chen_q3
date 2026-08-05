-- observability.db — disposable, rebuildable state for Q3 sensors and runtime metrics.
--
-- This database is deliberately separate from knowledge.db.  Raw holes, import
-- edges, taint propagation and timing rows have no reason/rollback/replacement
-- semantics.  They may inform a reviewed knowledge journal entry, but are not
-- themselves durable project decisions or proof truth.

PRAGMA foreign_keys = ON;
PRAGMA user_version = 6;

CREATE TABLE snapshot (
    id             TEXT PRIMARY KEY,
    schema_version INTEGER NOT NULL,
    generated_at   TEXT NOT NULL,
    source_commit  TEXT NOT NULL,
    status         TEXT NOT NULL
);

CREATE TABLE source_state (
    snapshot_id         TEXT NOT NULL,
    source_id           TEXT NOT NULL,
    kind                TEXT NOT NULL,
    path                TEXT NOT NULL,
    sha256              TEXT,
    source_generated_at TEXT,
    observed_mtime      TEXT,
    record_count        INTEGER NOT NULL,
    stale               INTEGER NOT NULL CHECK (stale IN (0, 1)),
    parse_status        TEXT NOT NULL,
    health_status       TEXT NOT NULL,
    note                TEXT,
    PRIMARY KEY (snapshot_id, source_id),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE file_state (
    snapshot_id       TEXT NOT NULL,
    file_id           TEXT NOT NULL,
    module            TEXT,
    direct_status     TEXT,
    propagation_status TEXT,
    integrity_status  TEXT,
    numeric_status    TEXT,
    intrinsic_risk    REAL,
    risk_score        REAL,
    risk_threshold    REAL,
    risk_status       TEXT,
    risk_exceeds      INTEGER CHECK (risk_exceeds IN (0, 1)),
    is_doomed         INTEGER CHECK (is_doomed IN (0, 1)),
    taint_origin_count INTEGER,
    root_ids_json      TEXT NOT NULL,
    unresolved_json    TEXT NOT NULL,
    PRIMARY KEY (snapshot_id, file_id),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE import_edge (
    snapshot_id TEXT NOT NULL,
    file_id     TEXT NOT NULL,
    dependency  TEXT NOT NULL,
    PRIMARY KEY (snapshot_id, file_id, dependency),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE sorry_site (
    snapshot_id TEXT NOT NULL,
    file_id     TEXT NOT NULL,
    line        INTEGER NOT NULL,
    PRIMARY KEY (snapshot_id, file_id, line),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE proof_root (
    snapshot_id         TEXT NOT NULL,
    root_id             TEXT NOT NULL,
    entry_file          TEXT,
    closure_files       INTEGER,
    axiom_count         INTEGER,
    project_axiom_count INTEGER,
    sorry_sites         INTEGER,
    tainted_files       INTEGER,
    PRIMARY KEY (snapshot_id, root_id),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE root_membership (
    snapshot_id TEXT NOT NULL,
    root_id     TEXT NOT NULL,
    file_id     TEXT NOT NULL,
    depth       INTEGER NOT NULL CHECK (depth >= 0),
    PRIMARY KEY (snapshot_id, root_id, file_id),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE taint_edge (
    snapshot_id TEXT NOT NULL,
    file_id     TEXT NOT NULL,
    source_file TEXT NOT NULL,
    PRIMARY KEY (snapshot_id, file_id, source_file),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE taint_root (
    snapshot_id TEXT NOT NULL,
    file_id     TEXT NOT NULL,
    root_name   TEXT NOT NULL,
    PRIMARY KEY (snapshot_id, file_id, root_name),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE axiom_dependency (
    snapshot_id     TEXT NOT NULL,
    root_id         TEXT NOT NULL,
    axiom_name      TEXT NOT NULL,
    source_file     TEXT,
    classification  TEXT NOT NULL,
    mapping_status  TEXT NOT NULL,
    candidates_json TEXT NOT NULL,
    axioms_json     TEXT NOT NULL,
    sorries_json    TEXT NOT NULL,
    PRIMARY KEY (snapshot_id, root_id, axiom_name),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE proof_node (
    snapshot_id        TEXT NOT NULL,
    root_id            TEXT NOT NULL,
    node_id            TEXT NOT NULL,
    classification     TEXT NOT NULL,
    mapping_status     TEXT NOT NULL,
    status             TEXT,
    source_file        TEXT,
    root_reachable     INTEGER CHECK (root_reachable IN (0, 1)),
    direct_status      TEXT,
    propagation_status TEXT,
    integrity_status   TEXT,
    numeric_status     TEXT,
    risk_score         REAL,
    risk_status        TEXT,
    risk_exceeds       INTEGER CHECK (risk_exceeds IN (0, 1)),
    is_doomed          INTEGER CHECK (is_doomed IN (0, 1)),
    alternatives_json  TEXT NOT NULL,
    PRIMARY KEY (snapshot_id, root_id, node_id),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE numeric_check (
    snapshot_id  TEXT NOT NULL,
    check_id     TEXT NOT NULL,
    evidence_class TEXT NOT NULL,
    status       TEXT,
    command_json TEXT NOT NULL,
    cwd          TEXT,
    exit_code    INTEGER,
    duration_s   REAL,
    timed_out    INTEGER NOT NULL CHECK (timed_out IN (0, 1)),
    stdout_sha256 TEXT,
    stderr_sha256 TEXT,
    notes        TEXT,
    PRIMARY KEY (snapshot_id, check_id),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE proshka_run (
    transaction_id       TEXT PRIMARY KEY,
    snapshot_id          TEXT NOT NULL,
    heading              TEXT NOT NULL,
    proof_address        TEXT,
    front                TEXT,
    conversation_id      TEXT,
    request_message_id   TEXT,
    sent_at              TEXT,
    completed_at         TEXT,
    wall_seconds         INTEGER,
    wall_is_lower_bound  INTEGER NOT NULL CHECK (wall_is_lower_bound IN (0, 1)),
    wall_human           TEXT,
    answer_now_shown     INTEGER CHECK (answer_now_shown IN (0, 1)),
    answer_now_clicked   INTEGER CHECK (answer_now_clicked IN (0, 1)),
    primary_result       TEXT,
    status               TEXT,
    result_pointer       TEXT,
    notes                TEXT,
    source_file          TEXT NOT NULL,
    source_line_start    INTEGER NOT NULL,
    raw_sha256           TEXT NOT NULL,
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE autopsy_event (
    snapshot_id          TEXT NOT NULL,
    event_id             TEXT NOT NULL,
    source_file          TEXT NOT NULL,
    source_line          INTEGER NOT NULL,
    goal_id              TEXT NOT NULL,
    front                TEXT NOT NULL,
    dropped_tag          TEXT NOT NULL,
    note                 TEXT NOT NULL,
    shape_discriminator  TEXT,
    structured           INTEGER NOT NULL CHECK (structured IN (0, 1)),
    namewatch_eligible   INTEGER NOT NULL CHECK (namewatch_eligible IN (0, 1)),
    raw_sha256           TEXT NOT NULL,
    authority            TEXT NOT NULL,
    PRIMARY KEY (snapshot_id, event_id),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE wall_state (
    snapshot_id       TEXT NOT NULL,
    wall_id           TEXT NOT NULL,
    dropped_tag       TEXT NOT NULL,
    dropped_structure TEXT NOT NULL,
    coverage_tags_json TEXT NOT NULL,
    fronts_json       TEXT NOT NULL,
    goals_json        TEXT NOT NULL,
    candidate_card    TEXT,
    status            TEXT NOT NULL,
    event_count       INTEGER NOT NULL,
    authority         TEXT NOT NULL,
    PRIMARY KEY (snapshot_id, wall_id),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE TABLE namewatch_candidate (
    snapshot_id       TEXT NOT NULL,
    candidate_id      TEXT NOT NULL,
    dropped_tag       TEXT NOT NULL,
    shape_discriminator TEXT NOT NULL,
    goals_json        TEXT NOT NULL,
    fronts_json       TEXT NOT NULL,
    event_count       INTEGER NOT NULL,
    status            TEXT NOT NULL,
    reason            TEXT NOT NULL,
    auto_promoted     INTEGER NOT NULL CHECK (auto_promoted IN (0, 1)),
    authority         TEXT NOT NULL,
    PRIMARY KEY (snapshot_id, candidate_id),
    FOREIGN KEY (snapshot_id) REFERENCES snapshot(id) ON DELETE CASCADE
);

CREATE INDEX idx_source_state_stale ON source_state(stale, source_id);
CREATE INDEX idx_file_state_propagation ON file_state(propagation_status);
CREATE INDEX idx_sorry_site_file ON sorry_site(file_id);
CREATE INDEX idx_root_membership_file ON root_membership(file_id, root_id);
CREATE INDEX idx_proshka_run_front ON proshka_run(front);
CREATE INDEX idx_proshka_run_completed ON proshka_run(completed_at);
CREATE INDEX idx_autopsy_tag ON autopsy_event(dropped_tag, shape_discriminator);
CREATE INDEX idx_wall_status ON wall_state(status);
CREATE INDEX idx_namewatch_status ON namewatch_candidate(status);
