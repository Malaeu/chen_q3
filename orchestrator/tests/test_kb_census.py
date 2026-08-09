import argparse
import sqlite3
import sys
from pathlib import Path


ORCHESTRATOR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ORCHESTRATOR))

import kb  # noqa: E402


def test_census_counts_search_sessions(tmp_path, monkeypatch, capsys):
    db_path = tmp_path / "knowledge.db"
    conn = sqlite3.connect(db_path)
    conn.executescript(
        """
        CREATE TABLE source_ledger (
            source_file TEXT PRIMARY KEY,
            expected_rows INTEGER NOT NULL,
            migrated_at TEXT NOT NULL,
            note TEXT
        );
        CREATE TABLE kill (source_file TEXT);
        CREATE TABLE move (source_file TEXT);
        CREATE TABLE journal_entry (source_file TEXT);
        CREATE TABLE dossier (source_file TEXT);
        CREATE TABLE postmortem (source_file TEXT);
        CREATE TABLE search_session (source_file TEXT);
        CREATE TABLE link (source_file TEXT);
        CREATE TABLE kill_alias (id TEXT);
        CREATE TABLE kill_evidence (id TEXT);

        INSERT INTO source_ledger VALUES ('oracle_questions', 2, '2026-08-06', 'test');
        INSERT INTO search_session VALUES ('oracle_questions/first.md');
        INSERT INTO search_session VALUES ('oracle_questions/second.md');
        """
    )
    conn.commit()
    conn.close()

    monkeypatch.setattr(kb, "DB_PATH", db_path)

    assert kb.cmd_census(argparse.Namespace()) == 0
    out = capsys.readouterr().out
    assert "oracle_questions" in out
    assert "DRIFT" not in out
    assert "search_session" in out
