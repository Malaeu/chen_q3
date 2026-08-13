"""AUTOPILOT_002 plants for refresh routing and semantic freshness."""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path

import pytest

from orchestrator import migration_census, spine
from scripts import q3_docs_corpus, search_external_lean

REPO = Path(__file__).resolve().parents[2]


def test_refresh_dispatch_is_closed_and_reason_specific() -> None:
    assert spine.refresh_actions("verdict-intake") == (
        "migrate-verdicts",
        "validate",
    )
    assert spine.refresh_actions("step-close") == (
        "migrate-verdicts",
        "migrate-journal",
        "migrate-progress-log",
        "semantic-index-if-stale",
        "validate",
    )
    assert spine.refresh_actions("semantic-index-refresh") == (
        "semantic-index",
        "validate",
    )
    goal_close = spine.refresh_actions("goal-close")
    assert goal_close[-7:] == (
        "backfill",
        "inventory",
        "atoms",
        "sensors",
        "semantic-index",
        "migration-census",
        "validate",
    )
    assert "migrate-journal" in goal_close
    assert "migrate-progress-log" in goal_close


def test_unknown_refresh_reason_fails_closed() -> None:
    with pytest.raises(spine.ControlViolation, match="SPINE_REFRESH_REASON_UNKNOWN"):
        spine.refresh_actions("typo-close")


def test_only_goal_close_refresh_materializes_spine_outputs() -> None:
    assert spine.refresh_writes_spine_outputs("goal-close") is True
    assert spine.refresh_writes_spine_outputs("verdict-intake") is False
    assert spine.refresh_writes_spine_outputs("step-close") is False
    assert spine.refresh_writes_spine_outputs("semantic-index-refresh") is False


def test_corpus_hash_is_path_and_byte_exact_but_mtime_independent(tmp_path: Path) -> None:
    first = tmp_path / "a.md"
    second = tmp_path / "nested" / "b.lean"
    second.parent.mkdir()
    first.write_text("same\n", encoding="utf-8")
    second.write_text("theorem b : True := by trivial\n", encoding="utf-8")
    files = [first, second]
    baseline = q3_docs_corpus.corpus_hash(files, tmp_path)
    os.utime(first, (1, 1))
    assert q3_docs_corpus.corpus_hash(list(reversed(files)), tmp_path) == baseline
    first.write_text("changed\n", encoding="utf-8")
    assert q3_docs_corpus.corpus_hash(files, tmp_path) != baseline
    first.write_text("same\n", encoding="utf-8")
    moved = tmp_path / "moved.md"
    first.rename(moved)
    assert q3_docs_corpus.corpus_hash([moved, second], tmp_path) != baseline


def test_foreign_machine_receipt_is_rejected(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = tmp_path / "source.md"
    source.write_text("current bytes\n", encoding="utf-8")
    snapshot = q3_docs_corpus.corpus_snapshot(tmp_path, [source])
    receipt = {
        "schema": "q3_semantic_index_receipt.v2",
        "status": "PASS",
        "collection": "q3_docs",
        "machine_id": "mac-receipt-not-this-linux-machine",
        "corpus": snapshot,
        "qmd_index": {"identity": "test-index"},
        "collection_file_count": snapshot["expected_collection_file_count"],
        "plants": [{"id": "fixed", "status": "PASS"}],
        "dynamic_queries": [{"id": "goal", "status": "PASS"}],
    }
    receipt_path = tmp_path / "receipt.json"
    receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
    monkeypatch.setattr(spine, "semantic_machine_id", lambda: "this-linux-machine")
    with pytest.raises(spine.ControlViolation, match="SEMANTIC_INDEX_LOCAL_RECEIPT_INVALID"):
        spine.validate_semantic_index(
            receipt_path=receipt_path,
            repo_root=tmp_path,
            files=[source],
            qmd_probe=lambda: {
                "identity": "test-index",
                "collection_file_count": snapshot["expected_collection_file_count"],
            },
        )


def test_deep_mode_runs_semantics_even_after_exact_hit(tmp_path: Path) -> None:
    fake = tmp_path / "oracle.py"
    fake.write_text(
        "import json\nprint(json.dumps([{'file':'qmd://q3_docs/deep-hit.md'}]))\n",
        encoding="utf-8",
    )
    env = os.environ.copy()
    env["Q3_RESEARCH_ORACLE_PY"] = str(fake)
    proc = subprocess.run(
        ["./ask.sh", "--deep", "SelectedTrialNormalizerBounded"],
        cwd=REPO,
        env=env,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "LEAN — объявления" in proc.stdout
    assert "СЕМАНТИЧЕСКИЙ ИНДЕКС q3_docs" in proc.stdout
    assert "deep-hit.md" in proc.stdout


def test_external_lean_registry_is_actually_queried(tmp_path: Path) -> None:
    base = tmp_path / "foreign"
    base.mkdir()
    (base / "Sylvester.lean").write_text(
        "theorem finrank_le_posIndex_of_posDefOn : True := by trivial\n",
        encoding="utf-8",
    )
    result = search_external_lean.search_registry(
        "posIndex positive inertia",
        bases=[("zeta23", base)],
    )
    assert result["bases_queried"] == ["zeta23"]
    assert result["matches"]
    assert result["matches"][0]["base_id"] == "zeta23"
    assert "Sylvester.lean" in result["matches"][0]["path"]


def test_migration_census_reports_source_database_and_unmigrated(tmp_path: Path) -> None:
    source_ids = {"a", "b", "c"}
    database_ids = {"a", "c"}
    row = migration_census.make_row("example", source_ids, database_ids)
    assert row == {
        "surface": "example",
        "source_rows": 3,
        "database_rows": 2,
        "unmigrated_rows": 1,
        "unmigrated_ids": ["b"],
    }


def test_large_qmd_embed_attempt_has_at_least_2400_seconds() -> None:
    refresh = load_refresh_module()
    assert refresh.QMD_EMBED_TIMEOUT_S >= 2400
    assert refresh.QMD_EMBED_RETRIES >= 5


def load_refresh_module():
    import importlib.util

    path = REPO / "q3.lean.aristotle" / "scripts" / "refresh_q3_docs.py"
    spec = importlib.util.spec_from_file_location("autopilot002_refresh_q3_docs", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
