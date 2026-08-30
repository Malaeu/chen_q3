import argparse
import json
import sqlite3
from pathlib import Path

from orchestrator import kb, migration_census, packet, spine


def test_insert_kills_supplies_non_death_scope_negation() -> None:
    conn = sqlite3.connect(":memory:")
    conn.executescript(kb.SCHEMA.read_text(encoding="utf-8"))
    row = {column: None for column in kb.KILL_COLUMNS}
    row.update(
        id="EXACT_ATTEMPT",
        unit_type="route",
        subject="theorem X direct route",
        status="killed",
        reason="exact source failed",
        source_file="test",
    )
    kb.insert_kills(conn, [row])
    scope = conn.execute(
        "SELECT scope_negation FROM kill WHERE id='EXACT_ATTEMPT'"
    ).fetchone()[0]
    assert "does not imply MATHEMATICALLY_DEAD" in scope
    assert "weaker consumer interfaces" in scope


def test_backfill_preserves_row_and_only_supplies_scope_negation() -> None:
    conn = sqlite3.connect(":memory:")
    conn.executescript(kb.SCHEMA.read_text(encoding="utf-8"))
    conn.execute(
        "INSERT INTO kill (id,unit_type,subject,status,reason,source_file) "
        "VALUES ('LEGACY','route','exact old attempt','killed','old reason','old source')"
    )
    changed = kb.backfill_operational_scope_negations(conn)
    row = conn.execute(
        "SELECT subject,status,reason,source_file,scope_negation FROM kill WHERE id='LEGACY'"
    ).fetchone()
    assert changed == 1
    assert row[:4] == ("exact old attempt", "killed", "old reason", "old source")
    assert "does not imply MATHEMATICALLY_DEAD" in row[4]


def test_official_and_class_aware_census_agree_on_dual_verdict(
    tmp_path: Path, monkeypatch, capsys,
) -> None:
    verdict = tmp_path / "PROSHKA_VERDICT_DUAL.md"
    verdict.write_text(
        "PRIMARY: KILL_EXACT\n"
        "iteration:\n"
        "  target: CONSUMER_Y\n"
        "  failed_strategy: DIRECT_X\n",
        encoding="utf-8",
    )
    db = tmp_path / "knowledge.db"
    conn = sqlite3.connect(db)
    conn.executescript(kb.SCHEMA.read_text(encoding="utf-8"))
    conn.execute("CREATE TABLE IF NOT EXISTS search_session (source_file TEXT)")
    source = f"docs/routeB_bus/proshka/{verdict.name}"
    rows = []
    for row_id, status in (("DUAL", "standing"), ("DUAL__VERDICT_KILL", "killed")):
        row = {column: None for column in kb.KILL_COLUMNS}
        row.update(
            id=row_id, unit_type="strategy" if status == "standing" else "route",
            subject=row_id, status=status, reason="fixture", source_file=source,
        )
        rows.append(row)
    kb.insert_kills(conn, rows)
    conn.execute(
        "INSERT INTO source_ledger (source_file,expected_rows,migrated_at,note) "
        "VALUES (?,?,?,?)", (source, 1, "2026-08-31", "wave 3 verdicts")
    )
    conn.commit()
    conn.close()

    monkeypatch.setattr(kb, "DB_PATH", db)
    monkeypatch.setattr(
        migration_census.kb_migrate_verdicts,
        "collect_files",
        lambda: {verdict.name: [verdict]},
    )
    monkeypatch.setattr(migration_census.kb_migrate_journal, "parse", lambda: ([], []))
    monkeypatch.setattr(migration_census.kb_migrate_progress_log, "parse_entries", lambda: [])

    class_aware = migration_census.census(db)
    assert class_aware["status"] == "PASS"
    assert kb.cmd_census(argparse.Namespace()) == 0
    output = capsys.readouterr().out
    assert "wave-3 verdict components (class-aware)" in output
    assert "class-aware migration census: PASS" in output
    assert "diagnostic only; not an equality authority" in output
    assert "missing operational scope negations 0" in output


def test_spine_projects_debt_and_death_as_distinct_canonical_classes(
    tmp_path: Path, monkeypatch,
) -> None:
    registry = tmp_path / "registry.json"
    registry.write_text(
        json.dumps(
            {
                "debts": [{
                    "id": "DEBT_X", "classification": "RESEARCH_DEBT",
                    "actual_consumer_requirement": "consumer Y",
                    "missing_object": "some sufficient Z",
                    "weaker_interface_probe": "try Z",
                }],
                "adjudications": [{
                    "id": "DEAD_Q", "classification": "MATHEMATICALLY_DEAD",
                    "scope": "exact Q only", "dead_reason": "counterexample",
                    "surviving_interface": "R survives",
                }],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(spine, "RESEARCH_DEPENDENCY_REGISTRY", registry)
    debt = "\n".join(spine._research_dependency_projection("RESEARCH_DEBT"))
    dead = "\n".join(spine._research_dependency_projection("MATHEMATICALLY_DEAD"))
    assert "DEBT_X" in debt and "DEAD_Q" not in debt
    assert "DEAD_Q" in dead and "DEBT_X" not in dead
    assert "consumer Y" in debt
    assert "exact Q only" in dead


def test_packet_includes_all_three_distinct_projection_sections(monkeypatch) -> None:
    fake_spine = "\n".join(
        [
            "## RESEARCH_DEBT (canonical research-dependency registry)",
            "- DEBT_X",
            "## MATHEMATICALLY_DEAD (canonical scoped adjudications)",
            "- DEAD_Q",
            "## Operational closures (legacy knowledge.db; not epistemic death)",
            "- KILL_EXACT_ATTEMPT",
            "## 3. Bus strategy memory (M3 iteration blocks in verdicts)",
            "- ITERATION_MEMORY",
        ]
    )
    monkeypatch.setattr(packet, "_fresh_spine_text", lambda: fake_spine)
    monkeypatch.setattr(packet, "_collect_goals", lambda: [])
    monkeypatch.setattr(packet, "_extract_governor_front", lambda: "front")
    monkeypatch.setattr(packet, "_postclose_guards", lambda: "guards")
    built = packet.build_packet("codex")
    assert "DEBT_X" in built
    assert "DEAD_Q" in built
    assert "KILL_EXACT_ATTEMPT" in built
    assert "Do not convert a legacy knowledge.db KILL" in built


def test_packet_refuses_controlling_proshka_clipboard_front_door() -> None:
    import pytest

    with pytest.raises(packet.PacketError, match="PROSHKA_PACKET_DISABLED") as exc:
        packet.build_packet("proshka")
    assert "workflow_runtime.py review-plan" in str(exc.value)
