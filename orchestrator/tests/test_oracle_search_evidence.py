from __future__ import annotations

import fcntl
import hashlib
import importlib.util
import json
import sys
from contextlib import contextmanager
from pathlib import Path

import pytest

from orchestrator import workflow_runtime
from scripts import literature_discovery, search_external_lean

SCRIPT = Path(__file__).resolve().parents[2] / "q3.lean.aristotle" / "scripts" / "oracle_questions.py"
SPEC = importlib.util.spec_from_file_location("q3_oracle_questions_test", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
oracle = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = oracle
SPEC.loader.exec_module(oracle)


def intent(*, admission: bool = False) -> dict[str, object]:
    row: dict[str, object] = {
        "schema": "q3_search_intent.v1",
        "mode": "ADMISSION" if admission else "DISCOVERY",
        "purpose": "RESOLVE_SUPPLIER",
        "goal_file": "docs/routeB_bus/058.goal.md",
        "goal_sha256": "a" * 64,
        "node_id": "NODE-058",
        "source_pin": "b" * 40,
        "terminal_consumer": "Q3.RouteB.consumer",
        "desired_consumer": {
            "object": "ground packet",
            "domain": "real line",
            "normalization": "unit norm",
            "quantifiers": "for every index",
            "assumptions": "simple even ground state",
            "output": "locally uniform convergence",
        },
        "admission": None,
        "canonical_terms": ["ground packet"],
        "alias_hypotheses": [],
        "known_false_friends": [{"term": "generic compactness", "reason": "wrong object", "source_ref": "card:old"}],
        "collections": ["q3_docs"],
        "network_policy": "FORBID",
    }
    if admission:
        row["admission"] = {
            "theorem": "Q3.RouteB.supplier",
            "consumer": "Q3.RouteB.consumer",
            "hypothesis_port": "hSupplier",
            "dependency_contract": {"schema": "test"},
            "source_blob": "c" * 40,
            "consumer_blob": "d" * 40,
            "target_declaration": "Q3.RouteB.supplier",
            "candidate_provenance": "SOURCE_DECLARED",
        }
    return row


def evidence(source: dict[str, object], *, decision: str = "LOCAL_COMPLETE_NO_EXACT_FIT") -> dict[str, object]:
    exact_fit = None
    if decision == "EXACT_FIT":
        exact_fit = {
            "status": "EXACT_FIT",
            "comparison": {
                "status": "EXACT_FIT",
                "candidate": {"name": "Q3.RouteB.supplier"},
                "target": {"name": "Q3.RouteB.supplier"},
            },
        }
    return {
        "schema": "q3_search_evidence.v1",
        "intent_id": oracle.canonical_hash(source),
        "observed_at": "2026-09-02T12:00:00+00:00",
        "mode": source["mode"],
        "purpose": source["purpose"],
        "status": "PASS",
        "decision": decision,
        "queries": [
            {
                "kind": kind,
                "query": query,
                "query_sha256": hashlib.sha256(query.encode()).hexdigest(),
            }
            for kind, query in (
                ("EXACT_NAME", "ground packet"),
                ("CONSUMER_SURFACE", "real line convergence"),
                ("THEOREM_SHAPE", "unit norm convergence"),
            )
        ],
        "metrics": {
            "qmd_subprocesses": 0,
            "external_lean_batches": 0,
            "web_batches": 0,
            "elapsed_seconds": 1.0,
        },
        "provider_ledger": [],
        "literature": [],
        "external_lean": None,
        "candidates": [],
        "alias_hypotheses": [],
        "exact_fit": exact_fit,
        "errors": [],
        "boundary": oracle.SEARCH_BOUNDARY,
    }


def q3_candidate() -> dict[str, object]:
    row: dict[str, object] = {
        "provider": "q3_docs",
        "query": "ground packet",
        "query_sha256": hashlib.sha256(b"ground packet").hexdigest(),
        "provider_id": "doc-1",
        "title": "ground packet",
        "excerpt": "compact convergence",
        "url": "local",
        "corpus_sha256": "c" * 64,
        "collection_identity": "d" * 64,
        "classification": "UNVERIFIED_CANDIDATE",
    }
    row["metadata_sha256"] = oracle.canonical_hash(
        {key: value for key, value in row.items() if key != "classification"}
    )
    return row


def card(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    journal = tmp_path / "oracle_questions"
    journal.mkdir()
    monkeypatch.setattr(oracle, "JOURNAL_DIR", journal)
    monkeypatch.setattr(
        oracle,
        "validate_search_intent_for_record",
        lambda value: json.loads(json.dumps(value)),
    )

    @contextmanager
    def unlocked():
        yield

    monkeypatch.setattr(oracle, "_search_evidence_writer_lock", unlocked)
    path = journal / "card.md"
    meta = {field: ([] if field in oracle.LIST_FIELDS else "") for field in oracle.FRONTMATTER_ORDER}
    meta.update({"status": "active", "main_address": "058.1", "blocker": "supplier"})
    path.write_text(oracle.serialize_frontmatter(meta) + "\n\nbody\n", encoding="utf-8")
    return path


def test_record_search_evidence_is_idempotent(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    path = card(tmp_path, monkeypatch)
    source = intent()
    result1 = oracle.record_search_evidence(path, source, evidence(source))
    bytes1 = path.read_bytes()
    result2 = oracle.record_search_evidence(path, source, evidence(source))
    assert result1[0] == "RECORDED"
    assert result2 == ("NOOP", result1[1])
    assert path.read_bytes() == bytes1


def test_zero_observation_never_populates_legacy_empty_terms(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    path = card(tmp_path, monkeypatch)
    source = intent()
    oracle.record_search_evidence(path, source, evidence(source))
    stored = oracle.read_card(path)
    assert oracle.ensure_list(stored.meta, "empty_terms") == []
    assert oracle.ensure_list(stored.meta, "false_friend_terms") == ["generic compactness"]


def test_exact_fit_marks_only_explicit_supplier_strong(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    path = card(tmp_path, monkeypatch)
    monkeypatch.setattr(
        oracle,
        "replay_exact_fit_for_record",
        lambda _intent: {"status": "EXACT_FIT"},
    )
    source = intent(admission=True)
    oracle.record_search_evidence(path, source, evidence(source, decision="EXACT_FIT"))
    stored = oracle.read_card(path)
    assert oracle.ensure_list(stored.meta, "strong_terms") == ["Q3.RouteB.supplier"]
    assert oracle.ensure_list(stored.meta, "opens_new_branch_terms") == []


def test_record_rejects_oversized_machine_block(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    path = card(tmp_path, monkeypatch)
    source = intent()
    payload = evidence(source)
    candidate = {
        "provider": "q3_docs",
        "query": "ground packet",
        "query_sha256": hashlib.sha256(b"ground packet").hexdigest(),
        "provider_id": "oversized",
        "title": "ground packet",
        "excerpt": "x" * (oracle.SEARCH_BLOCK_MAX_BYTES + 1),
        "url": "local",
        "corpus_sha256": "c" * 64,
        "collection_identity": "d" * 64,
        "classification": "UNVERIFIED_CANDIDATE",
    }
    candidate["metadata_sha256"] = oracle.canonical_hash(
        {key: value for key, value in candidate.items() if key != "classification"}
    )
    payload["candidates"] = [candidate]
    payload["decision"] = "CANDIDATES"
    with pytest.raises(ValueError, match="MACHINE_BLOCK_TOO_LARGE"):
        oracle.record_search_evidence(path, source, payload)


def test_fabricated_exact_fit_never_adds_strong_term(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = card(tmp_path, monkeypatch)
    source = intent(admission=True)
    monkeypatch.setattr(
        oracle,
        "replay_exact_fit_for_record",
        lambda _intent: {"status": "REJECTED"},
    )
    with pytest.raises(ValueError, match="EXACT_FIT_REPLAY_FAILED"):
        oracle.record_search_evidence(path, source, evidence(source, decision="EXACT_FIT"))
    assert oracle.ensure_list(oracle.read_card(path).meta, "strong_terms") == []


def test_intermediate_symlink_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    real = tmp_path / "real"
    real.mkdir()
    linked = tmp_path / "journal"
    linked.symlink_to(real, target_is_directory=True)
    monkeypatch.setattr(oracle, "JOURNAL_DIR", linked)
    target = linked / "card.md"
    (real / "card.md").write_text("body\n", encoding="utf-8")
    with pytest.raises(ValueError, match="SYMLINK_COMPONENT"):
        oracle._assert_no_symlink_components(target, linked)


def test_atomic_card_replace_rejects_input_cas_drift(tmp_path: Path) -> None:
    path = tmp_path / "card.md"
    path.write_text("current\n", encoding="utf-8")
    with pytest.raises(ValueError, match="CARD_INPUT_DRIFT"):
        oracle._atomic_card_replace(path, b"replacement\n", expected_sha256="0" * 64)
    assert path.read_text(encoding="utf-8") == "current\n"


def test_atomic_card_replace_preserves_mode_and_ownership(tmp_path: Path) -> None:
    path = tmp_path / "card.md"
    path.write_text("current\n", encoding="utf-8")
    path.chmod(0o664)
    before = path.stat()
    oracle._atomic_card_replace(
        path,
        b"replacement\n",
        expected_sha256=hashlib.sha256(b"current\n").hexdigest(),
    )
    after = path.stat()
    assert path.read_bytes() == b"replacement\n"
    assert after.st_mode & 0o777 == 0o664
    assert (after.st_uid, after.st_gid) == (before.st_uid, before.st_gid)


def test_search_evidence_writer_lock_fails_closed_when_busy(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    subprocess = __import__("subprocess")
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    lock = tmp_path / ".git/q3-three-body.writer.lock"
    lock.write_text("idle\n", encoding="utf-8")
    monkeypatch.setattr(oracle, "REPO_ROOT", tmp_path)
    with lock.open("r") as held:
        fcntl.flock(held.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(ValueError, match="WRITER_LOCK_BUSY"):
            with oracle._search_evidence_writer_lock():
                pass


def test_observation_identity_excludes_runtime_metrics() -> None:
    source = intent()
    first = evidence(source)
    second = evidence(source)
    first["provider_ledger"] = [{"provider": "q3_docs", "elapsed_seconds": 1.0}]
    second["provider_ledger"] = [{"provider": "q3_docs", "elapsed_seconds": 9.0}]
    assert oracle.search_observation_identity(
        first
    ) == oracle.search_observation_identity(second)
    assert workflow_runtime._search_observation_identity(
        first
    ) == oracle.search_observation_identity(first)


def test_durable_candidate_hash_and_decision_are_coherent() -> None:
    source = intent()
    payload = evidence(source, decision="CANDIDATES")
    payload["candidates"] = [q3_candidate()]
    assert oracle.validate_search_evidence(source, payload)["decision"] == "CANDIDATES"

    planted_hash = json.loads(json.dumps(payload))
    planted_hash["candidates"][0]["metadata_sha256"] = "0" * 64
    with pytest.raises(ValueError, match="CANDIDATE_RECEIPT_INVALID"):
        oracle.validate_search_evidence(source, planted_hash)

    planted_decision = json.loads(json.dumps(payload))
    planted_decision["decision"] = "LOCAL_COMPLETE_NO_EXACT_FIT"
    with pytest.raises(ValueError, match="DECISION_CANDIDATE_MISMATCH"):
        oracle.validate_search_evidence(source, planted_decision)


def test_inherited_writer_lock_requires_canonical_held_descriptor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    __import__("subprocess").run(["git", "init", "-q"], cwd=tmp_path, check=True)
    lock = tmp_path / ".git/q3-three-body.writer.lock"
    lock.write_text("writer\n", encoding="utf-8")
    monkeypatch.setattr(oracle, "REPO_ROOT", tmp_path)
    with lock.open("r") as held:
        with pytest.raises(ValueError, match="NOT_HELD"):
            oracle._validate_inherited_writer_lock(held.fileno())
        fcntl.flock(held.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        oracle._validate_inherited_writer_lock(held.fileno())
        fcntl.flock(held.fileno(), fcntl.LOCK_UN)

    other = tmp_path / "other.lock"
    other.write_text("other\n", encoding="utf-8")
    with other.open("r") as wrong:
        with pytest.raises(ValueError, match="IDENTITY_MISMATCH"):
            oracle._validate_inherited_writer_lock(wrong.fileno())


def test_durable_writer_replays_literature_receipt_validator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(literature_discovery, "_arxiv", lambda *_args, **_kwargs: [])
    receipt = literature_discovery.discover(
        ["ground packet"], providers=("arxiv",), timeout_seconds=1
    )
    receipt["query_family_sha256"] = "0" * 64
    source = intent()
    payload = evidence(source)
    payload["literature"] = [receipt]
    with pytest.raises(ValueError, match="LITERATURE_RECEIPT_INVALID"):
        oracle.validate_search_evidence(source, payload)


def test_durable_writer_replays_external_batch_validator(tmp_path: Path) -> None:
    root = tmp_path / "base"
    root.mkdir()
    (root / "Sample.lean").write_text(
        "theorem sample : True := by trivial\n", encoding="utf-8"
    )
    source = intent()
    payload = evidence(source)
    queries = [row["query"] for row in payload["queries"]]
    receipt = search_external_lean.search_registry_batch(
        queries,
        bases=[("sample", root)],
        enabled_ids=["sample"],
        budget_seconds=1,
    )
    receipt["registry_sha256"] = "0" * 64
    payload["external_lean"] = receipt
    payload["metrics"]["external_lean_batches"] = 1
    with pytest.raises(ValueError, match="EXTERNAL_RECEIPT_INVALID"):
        oracle.validate_search_evidence(source, payload)
