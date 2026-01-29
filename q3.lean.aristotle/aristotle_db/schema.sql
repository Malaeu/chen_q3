-- Aristotle Proofs Database Schema
-- Created: 2025-12-28
-- Purpose: Track Lean proofs from Aristotle for A3_FLOOR new kernel approach

-- Таблица документов (файлов)
CREATE TABLE IF NOT EXISTS docs (
    doc_id TEXT PRIMARY KEY,       -- e.g. "A3_FLOOR_v3", "PROJECT_SPECS"
    path TEXT NOT NULL,            -- full path to file
    approach TEXT NOT NULL,        -- NEW_KERNEL | OLD_RKHS
    priority TEXT NOT NULL,        -- HIGH | MEDIUM | LOW | DEPRECATED
    status TEXT NOT NULL,          -- proven | in_progress | todo | deprecated
    stage TEXT,                    -- Stage1..Stage4 or null (for A3_FLOOR files)
    source TEXT,                   -- aristotle | manual | spec
    aristotle_uuid TEXT,           -- UUID from Aristotle (if applicable)
    lines INTEGER,                 -- line count
    size_bytes INTEGER             -- file size
);

-- Таблица лемм/теорем
CREATE TABLE IF NOT EXISTS lemmas (
    lemma_id TEXT PRIMARY KEY,     -- e.g. "im_trigamma_neg_v3"
    name TEXT NOT NULL,            -- lemma name without version suffix
    doc_id TEXT NOT NULL,          -- FK to docs
    status TEXT NOT NULL,          -- proven | in_progress | todo | sorry
    priority TEXT NOT NULL,        -- HIGH | MEDIUM | LOW | DEPRECATED
    statement TEXT,                -- full lemma statement
    deps_json TEXT,                -- JSON array of dependencies ["trigamma_summable", ...]
    notes TEXT,                    -- any notes about tactics, approaches
    line_start INTEGER,            -- line number in file
    line_end INTEGER,              -- end line
    FOREIGN KEY (doc_id) REFERENCES docs(doc_id)
);

-- Таблица спецификаций (из docs/PROJECT_SPECS.md)
CREATE TABLE IF NOT EXISTS specs (
    spec_id TEXT PRIMARY KEY,      -- e.g. "c_star_value"
    section TEXT NOT NULL,         -- e.g. "§3", "§7"
    key TEXT NOT NULL,             -- e.g. "c_star", "sign"
    value TEXT NOT NULL,           -- e.g. "11/10", "Q = Q_arch - Q_prime"
    approach TEXT NOT NULL,        -- NEW_KERNEL (always for specs)
    source_path TEXT NOT NULL      -- path to source file
);

-- Индексы для быстрого поиска
CREATE INDEX IF NOT EXISTS idx_lemmas_name ON lemmas(name);
CREATE INDEX IF NOT EXISTS idx_lemmas_status ON lemmas(status);
CREATE INDEX IF NOT EXISTS idx_lemmas_priority ON lemmas(priority);
CREATE INDEX IF NOT EXISTS idx_docs_approach ON docs(approach);
CREATE INDEX IF NOT EXISTS idx_docs_priority ON docs(priority);
CREATE INDEX IF NOT EXISTS idx_specs_section ON specs(section);
