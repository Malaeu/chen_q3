
-- ============================================================================
-- WAVE 4 (2026-08-06): search sessions — the owner's original "flags on the map".
--
-- 60 oracle cards from April 2026, never migrated. Their point was never the answer:
-- it was the RECORD OF THE SEARCH — which terms worked, which returned nothing, which
-- looked right and led astray. That is the only place in the project where positive
-- search experience was kept, and the only contour holding an ADDRESS system tying a
-- question to a node of the proof tree.
--
-- Three questions this makes answerable and nothing else can:
--   * "did we already work this address / this blocker?"
--   * "which words does one use to search this in THIS project?"
--   * "which words look right and waste a day?"
-- ============================================================================

CREATE TABLE IF NOT EXISTS search_session (
    id            TEXT PRIMARY KEY,
    date          TEXT,
    main_address  TEXT,          -- PO3a.3, D2, H-bridge.11 …
    address_status TEXT,         -- active | closed | …
    status        TEXT,
    blocker       TEXT,          -- the precise question this search was opened for
    raw_notation  TEXT,          -- address notation as written by hand
    collections   TEXT,          -- q3_docs | math_papers | web  (source-agnostic by design)
    tags          TEXT,
    body_md       TEXT,
    source_file   TEXT NOT NULL
);

-- The trained vocabulary. verdict is the whole value of the table.
CREATE TABLE IF NOT EXISTS search_term (
    session_id TEXT NOT NULL,
    term       TEXT NOT NULL,
    verdict    TEXT NOT NULL,   -- strong | empty | false_friend | opens_branch
    PRIMARY KEY (session_id, term, verdict),
    FOREIGN KEY (session_id) REFERENCES search_session(id)
);

-- Address graph: one session touches several nodes in different roles.
CREATE TABLE IF NOT EXISTS search_address (
    session_id TEXT NOT NULL,
    address    TEXT NOT NULL,
    role       TEXT NOT NULL,   -- main | related | ancestor | child | neighbor | normalized
    PRIMARY KEY (session_id, address, role),
    FOREIGN KEY (session_id) REFERENCES search_session(id)
);

CREATE TABLE IF NOT EXISTS search_link (
    session_id TEXT NOT NULL,
    kind       TEXT NOT NULL,   -- insight | request_node
    ref        TEXT NOT NULL,
    PRIMARY KEY (session_id, kind, ref),
    FOREIGN KEY (session_id) REFERENCES search_session(id)
);

CREATE INDEX IF NOT EXISTS idx_term_verdict  ON search_term(verdict);
CREATE INDEX IF NOT EXISTS idx_term_term     ON search_term(term);
CREATE INDEX IF NOT EXISTS idx_addr_address  ON search_address(address);
CREATE INDEX IF NOT EXISTS idx_sess_address  ON search_session(main_address);

CREATE VIRTUAL TABLE IF NOT EXISTS search_fts USING fts5(
    blocker, body_md, main_address, content='search_session', content_rowid='rowid');
