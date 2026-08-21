"""AUTOPILOT_002 plants for refresh routing and semantic freshness."""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

from orchestrator import migration_census, spine
from scripts import deep_preflight, q3_docs_corpus, qmd_ops, search_external_lean

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
    assert result["matches"][0]["match_kind"] == "TEXT_CANDIDATE"
    assert "Sylvester.lean" in result["matches"][0]["path"]


def test_external_registry_queries_every_enabled_base_even_after_match_limit(
    tmp_path: Path,
) -> None:
    first = tmp_path / "first"
    second = tmp_path / "second"
    first.mkdir()
    second.mkdir()
    (first / "One.lean").write_text("theorem needle : True := by trivial\n")
    (second / "Two.lean").write_text("theorem needle : True := by trivial\n")
    result = search_external_lean.search_registry(
        "needle", bases=[("first", first), ("second", second)], max_matches=1
    )
    assert result["bases_queried"] == ["first", "second"]
    assert len(result["matches"]) == 1
    assert result["errors"] == []


def test_external_registry_missing_enabled_base_is_incomplete(tmp_path: Path) -> None:
    first = tmp_path / "first"
    first.mkdir()
    (first / "One.lean").write_text("theorem needle : True := by trivial\n")
    result = search_external_lean.search_registry(
        "needle",
        bases=[("first", first)],
        enabled_ids=["first", "missing"],
    )
    assert "enabled bases not resolved: missing" in result["errors"]


def test_dynamic_goal_path_match_uses_qmd_slug_punctuation(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    goal = tmp_path / "058_realzero_ground_diagonal_to_xi.goal.md"
    goal.write_text("goal\n", encoding="utf-8")
    monkeypatch.setattr(deep_preflight, "REPO", tmp_path)
    monkeypatch.setattr(
        deep_preflight,
        "_semantic_query",
        lambda _query: [
            {
                "file": (
                    "qmd://q3_docs/docs/routeb-bus/"
                    "058-realzero-ground-diagonal-to-xi-goal.md"
                )
            }
        ],
    )
    monkeypatch.setattr(
        deep_preflight.search_external_lean,
        "search_registry",
        lambda _query: {
            "bases_queried": ["zeta23"],
            "boundary": "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE",
            "errors": [],
            "matches": [],
        },
    )

    result = deep_preflight.run_preflight(
        goal_path=goal,
        query_specs=[
            {
                "id": "goal",
                "query": "GOAL 058 REALZERO_GROUND_DIAGONAL_TO_XI",
                "expected_path_token": goal.name.replace("_", "-").lower(),
            }
        ],
    )

    assert result["status"] == "PASS"
    assert result["queries"][0]["expected_path_token"] == (
        "058-realzero-ground-diagonal-to-xi-goal-md"
    )
    assert result["queries"][0]["expected_path_match"] is True


def test_dynamic_expected_path_uses_bounded_lexical_fallback(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    goal = tmp_path / "058_realzero_ground_diagonal_to_xi.goal.md"
    goal.write_text("goal\n", encoding="utf-8")
    monkeypatch.setattr(deep_preflight, "REPO", tmp_path)
    monkeypatch.setattr(
        deep_preflight,
        "_semantic_query",
        lambda _query: [{"file": "qmd://q3_docs/docs/context-only.md"}],
    )
    monkeypatch.setattr(
        deep_preflight,
        "_lexical_query",
        lambda _query: [
            {
                "file": (
                    "qmd://q3_docs/q3-lean-aristotle/q3/proofs/routeb/"
                    "proposition59groundlagrangezerosetbridge.lean"
                )
            }
        ],
    )
    monkeypatch.setattr(
        deep_preflight.search_external_lean,
        "search_registry",
        lambda _query: {
            "bases_queried": ["zeta23"],
            "boundary": "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE",
            "errors": [],
            "matches": [],
        },
    )

    result = deep_preflight.run_preflight(
        goal_path=goal,
        query_specs=[
            {
                "id": "exact_target",
                "query": "Proposition59GroundLagrangeZeroSetBridge",
                "expected_path_token": "proposition59groundlagrangezerosetbridge",
            }
        ],
    )

    assert result["status"] == "PASS"
    row = result["queries"][0]
    assert row["expected_path_match"] is True
    assert row["result_count"] == 2
    assert row["top_paths"][-1].endswith(
        "proposition59groundlagrangezerosetbridge.lean"
    )


def test_dynamic_expected_path_uses_corpus_inventory_after_lexical_miss(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    goal = tmp_path / "058_realzero_ground_diagonal_to_xi.goal.md"
    goal.write_text("goal\n", encoding="utf-8")
    monkeypatch.setattr(deep_preflight, "REPO", tmp_path)
    monkeypatch.setattr(
        deep_preflight,
        "_semantic_query",
        lambda _query: [{"file": "qmd://q3_docs/docs/context-only.md"}],
    )
    monkeypatch.setattr(
        deep_preflight,
        "_lexical_query",
        lambda _query: [{"file": "qmd://q3_docs/docs/importer-only.md"}],
    )
    monkeypatch.setattr(
        deep_preflight,
        "_corpus_path_query",
        lambda _token: [
            {
                "file": (
                    "qmd://q3_docs/q3-lean-aristotle/q3/proofs/routeb/"
                    "proposition59groundlagrangezerosetbridge.lean"
                )
            }
        ],
    )
    monkeypatch.setattr(
        deep_preflight.search_external_lean,
        "search_registry",
        lambda _query: {
            "bases_queried": ["zeta23"],
            "boundary": "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE",
            "errors": [],
            "matches": [],
        },
    )

    result = deep_preflight.run_preflight(
        goal_path=goal,
        query_specs=[
            {
                "id": "exact_target",
                "query": "Proposition59GroundLagrangeZeroSetBridge",
                "expected_path_token": "proposition59groundlagrangezerosetbridge",
            }
        ],
    )

    assert result["status"] == "PASS"
    row = result["queries"][0]
    assert row["expected_path_match"] is True
    assert row["result_count"] == 3
    assert row["top_paths"][-1].endswith(
        "proposition59groundlagrangezerosetbridge.lean"
    )


def test_empty_semantic_query_is_retried(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    responses = iter(
        [
            SimpleNamespace(returncode=0, stdout="[]", stderr=""),
            SimpleNamespace(
                returncode=0,
                stdout=json.dumps([{"file": "qmd://q3_docs/live.md"}]),
                stderr="",
            ),
        ]
    )
    sleeps: list[int] = []
    monkeypatch.setattr(
        deep_preflight.subprocess,
        "run",
        lambda *args, **kwargs: next(responses),
    )
    monkeypatch.setattr(deep_preflight.time, "sleep", sleeps.append)
    assert deep_preflight._semantic_query("GOAL 058") == [
        {"file": "qmd://q3_docs/live.md"}
    ]
    assert sleeps == [1]


def test_known_bun_napi_finalizer_crash_is_retried(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    responses = iter(
        [
            SimpleNamespace(
                returncode=-6,
                stdout="",
                stderr=(
                    "Attempted to call a non-GC-safe function inside a NAPI finalizer\n"
                    "Bun has crashed"
                ),
            ),
            SimpleNamespace(returncode=0, stdout='[{"file":"live.md"}]', stderr=""),
        ]
    )
    sleeps: list[float] = []
    monkeypatch.setattr(qmd_ops.subprocess, "run", lambda *args, **kwargs: next(responses))
    monkeypatch.setattr(qmd_ops.time, "sleep", sleeps.append)
    assert qmd_ops.run_qmd(["qmd", "vsearch", "plant"], retries=1) == (
        '[{"file":"live.md"}]'
    )
    assert sleeps == [0.5]


def test_complete_vsearch_json_survives_post_output_bun_crash(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    response = SimpleNamespace(
        returncode=132,
        stdout=(
            "Expanding query...\nSearching 3 vector queries...\n"
            '[{"file":"qmd://q3_docs/live.md"}]\n'
        ),
        stderr=(
            "Attempted to call a non-GC-safe function inside a NAPI finalizer\n"
            "Bun has crashed"
        ),
    )
    monkeypatch.setattr(qmd_ops.subprocess, "run", lambda *args, **kwargs: response)
    assert qmd_ops.run_qmd(["qmd", "vsearch", "plant"]) == response.stdout


def test_incomplete_vsearch_json_still_fails_closed_after_bun_crash(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    response = SimpleNamespace(
        returncode=132,
        stdout='[{"file":"qmd://q3_docs/live.md"}',
        stderr=(
            "Attempted to call a non-GC-safe function inside a NAPI finalizer\n"
            "Bun has crashed"
        ),
    )
    monkeypatch.setattr(qmd_ops.subprocess, "run", lambda *args, **kwargs: response)
    monkeypatch.setattr(qmd_ops.time, "sleep", lambda _: None)
    with pytest.raises(RuntimeError, match="Bun has crashed"):
        qmd_ops.run_qmd(["qmd", "vsearch", "plant"], retries=1)


def test_unknown_qmd_failure_remains_fail_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0

    def fail(*args: object, **kwargs: object) -> SimpleNamespace:
        nonlocal calls
        calls += 1
        return SimpleNamespace(returncode=2, stdout="", stderr="ordinary failure")

    monkeypatch.setattr(qmd_ops.subprocess, "run", fail)
    with pytest.raises(RuntimeError, match="ordinary failure"):
        qmd_ops.run_qmd(["qmd", "vsearch", "plant"], retries=4)
    assert calls == 1


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
        "stale_rows": 0,
        "stale_ids": [],
    }


def test_migration_census_reports_stale_database_rows() -> None:
    row = migration_census.make_row("example", {"a"}, {"a", "old"})
    assert row["stale_rows"] == 1
    assert row["stale_ids"] == ["old"]


def test_step_close_requires_attempt_and_other_reasons_forbid_payloads(
    tmp_path: Path,
) -> None:
    with pytest.raises(spine.ControlViolation, match="GOAL_ATTEMPT_EVENT_REQUIRED"):
        spine._validate_refresh_payloads("step-close", None, None)
    payload = tmp_path / "attempt.json"
    payload.write_text("{}", encoding="utf-8")
    with pytest.raises(spine.ControlViolation, match="SPINE_REFRESH_PAYLOAD_FORBIDDEN"):
        spine._validate_refresh_payloads("goal-close", payload, None)


def test_step_close_records_events_before_migrations(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    attempt = tmp_path / "attempt.json"
    insight = tmp_path / "insight.json"
    attempt.write_text("{}", encoding="utf-8")
    insight.write_text("{}", encoding="utf-8")
    calls: list[str] = []
    monkeypatch.setattr(
        spine,
        "refresh_actions",
        lambda reason: ("migrate-journal", "validate") if reason == "step-close" else (),
    )
    monkeypatch.setattr(
        spine,
        "_run_checked",
        lambda action, _command: calls.append(action),
    )
    spine.execute_refresh(
        "step-close", attempt_payload=attempt, insight_payload=insight
    )
    assert calls == ["record-attempt", "record-insight", "migrate-journal"]


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
