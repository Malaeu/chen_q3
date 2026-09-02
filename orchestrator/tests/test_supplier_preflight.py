"""Plants for the complete shelf, EnvDump properties, and generic type-fit chain."""

from __future__ import annotations

import hashlib
import json
import subprocess
import time
from pathlib import Path
from types import SimpleNamespace

import pytest

from docs.cartographer.comparator import fit
from scripts import literature_discovery, search_external_lean, supplier_preflight


def search_intent(*, mode: str = "DISCOVERY", purpose: str = "RESOLVE_SUPPLIER", network: str = "FORBID") -> dict[str, object]:
    payload: dict[str, object] = {
        "schema": "q3_search_intent.v1",
        "mode": mode,
        "purpose": purpose,
        "goal_file": "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md",
        "goal_sha256": "a" * 64,
        "node_id": "REALZERO_GROUND_DIAGONAL_TO_XI",
        "source_pin": "b" * 40,
        "terminal_consumer": "Q3.RouteB.consumer",
        "desired_consumer": {
            "object": "ground packet",
            "domain": "real line",
            "normalization": "unit norm",
            "quantifiers": "for every cofinal index",
            "assumptions": "simple even ground state",
            "output": "locally uniform convergence",
        },
        "admission": None,
        "canonical_terms": ["ground packet", "locally uniform convergence"],
        "alias_hypotheses": [
            {"kind": "CHARACTERIZATION", "term": "compact convergence", "language": "en", "provenance": "owner", "preserves": ["domain", "output"]},
            {"kind": "DUAL", "term": "spectral transform", "language": "en", "provenance": "owner", "preserves": ["object"]},
        ],
        "known_false_friends": [{"term": "generic compactness", "reason": "wrong object", "source_ref": "old-card"}],
        "collections": ["q3_docs", "math_papers", "zotero_lib"],
        "network_policy": network,
    }
    if mode == "ADMISSION":
        payload["admission"] = {
            "theorem": "Q3.RouteB.supplier",
            "consumer": "Q3.RouteB.consumer",
            "hypothesis_port": "hSupplier",
            "dependency_contract": {"schema": "test"},
            "source_blob": "c" * 40,
            "consumer_blob": "d" * 40,
            "target_declaration": "Q3.RouteB.target",
            "target_type_sha256": supplier_preflight._canonical_hash(
                {"name": "Q3.RouteB.target", "type": "True"}
            ),
            "candidate_provenance": "SOURCE_DECLARED",
        }
    return payload


def test_search_intent_closed_schema_and_modes() -> None:
    assert supplier_preflight.validate_search_intent(search_intent())["mode"] == "DISCOVERY"
    assert supplier_preflight.validate_search_intent(search_intent(mode="ADMISSION"))["admission"] is not None
    planted = search_intent()
    planted["unexpected"] = True
    with pytest.raises(supplier_preflight.SearchIntentError, match="exactly"):
        supplier_preflight.validate_search_intent(planted)
    planted = search_intent(mode="ADMISSION")
    planted["admission"]["target_declaration"] = planted["admission"]["theorem"]
    with pytest.raises(supplier_preflight.SearchIntentError, match="MUST_BE_DISTINCT"):
        supplier_preflight.validate_search_intent(planted)


def _runtime_search_fixture(tmp_path: Path, *, admission: bool) -> dict[str, object]:
    goal = tmp_path / "docs/routeB_bus/058_live.goal.md"
    source = tmp_path / "q3.lean.aristotle/Q3/Source.lean"
    consumer = tmp_path / "q3.lean.aristotle/Q3/Consumer.lean"
    registry = tmp_path / "orchestrator/state/NODE_REGISTRY_V10.json"
    for path in (goal, source, consumer, registry):
        path.parent.mkdir(parents=True, exist_ok=True)
    source.write_text("theorem supplier : True := by trivial\n", encoding="utf-8")
    consumer.write_text("theorem consumer : True := supplier\n", encoding="utf-8")
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "q3.lean.aristotle"], cwd=tmp_path, check=True)
    subprocess.run(
        [
            "git", "-c", "user.name=Plant", "-c", "user.email=p@example.invalid",
            "commit", "-qm", "source",
        ],
        cwd=tmp_path,
        check=True,
    )
    source_pin = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=tmp_path, check=True,
        capture_output=True, text=True,
    ).stdout.strip()
    source_blob = supplier_preflight._git_blob(source)
    consumer_blob = supplier_preflight._git_blob(consumer)
    goal.write_text(
        "```yaml\nSTATUS: OPEN\nNODE: NODE-058\nSOURCE_PIN: "
        + source_pin
        + "\nTHEOREM: Q3.RouteB.supplier\n"
        "TERMINAL_CONSUMER: Q3.RouteB.consumer\n```\n",
        encoding="utf-8",
    )
    payload = search_intent(mode="ADMISSION" if admission else "DISCOVERY")
    payload["goal_file"] = goal.relative_to(tmp_path).as_posix()
    payload["goal_sha256"] = hashlib.sha256(goal.read_bytes()).hexdigest()
    payload["node_id"] = "NODE-058"
    payload["source_pin"] = source_pin
    if admission:
        edge_contract = {
            "edge_id": "E058",
            "theorem": "Q3.RouteB.supplier",
            "consumer": "Q3.RouteB.consumer",
            "hypothesis_port": "Q3.RouteB.supplier",
            "target_declaration": "Q3.RouteB.target",
            "target_type_sha256": payload["admission"]["target_type_sha256"],
        }
        payload["admission"] = {
            **payload["admission"],
            "hypothesis_port": "Q3.RouteB.supplier",
            "dependency_contract": edge_contract,
            "source_blob": source_blob,
            "consumer_blob": consumer_blob,
        }
        registry.write_text(
            json.dumps(
                {
                    "schema": "q3_node_registry.v10",
                    "nodes": [
                        {
                            "node_id": "NODE-058",
                            "theorem_ids": ["Q3.RouteB.supplier"],
                            "terminal_consumer": ["Q3.RouteB.consumer"],
                            "source": {
                                "path": source.relative_to(tmp_path).as_posix(),
                                "blob": source_blob,
                                "commit": source_pin,
                            },
                        }
                    ],
                    "edges": [
                        {
                            **edge_contract,
                            "consumer_path": consumer.relative_to(tmp_path).as_posix(),
                            "consumer_blob": consumer_blob,
                            "hypothesis_port": {
                                "direct_reference": "Q3.RouteB.supplier",
                                "surface": "ELABORATED_VALUE",
                                "challenge_declaration": "Q3.RouteB.target",
                                "challenge_type_sha256": payload["admission"]["target_type_sha256"],
                            },
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
    return payload


def test_search_intent_runtime_binds_physical_goal_and_exact_edge(tmp_path: Path) -> None:
    payload = _runtime_search_fixture(tmp_path, admission=True)
    assert supplier_preflight.validate_search_intent_runtime(payload, repo=tmp_path) == payload


def test_search_intent_runtime_rejects_goal_and_consumer_blob_drift(tmp_path: Path) -> None:
    original = _runtime_search_fixture(tmp_path, admission=True)
    payload = json.loads(json.dumps(original))
    payload["goal_sha256"] = "0" * 64
    with pytest.raises(supplier_preflight.SearchIntentError, match="GOAL_BLOB_DRIFT"):
        supplier_preflight.validate_search_intent_runtime(payload, repo=tmp_path)
    payload = json.loads(json.dumps(original))
    payload["admission"]["consumer_blob"] = "0" * 40
    with pytest.raises(supplier_preflight.SearchIntentError, match="BLOB_OR_PORT_DRIFT"):
        supplier_preflight.validate_search_intent_runtime(payload, repo=tmp_path)


def test_search_intent_runtime_rejects_terminal_consumer_drift_in_discovery(
    tmp_path: Path,
) -> None:
    payload = _runtime_search_fixture(tmp_path, admission=False)
    payload["terminal_consumer"] = "Q3.RouteB.unrelatedConsumer"
    with pytest.raises(
        supplier_preflight.SearchIntentError, match="TERMINAL_CONSUMER_DRIFT"
    ):
        supplier_preflight.validate_search_intent_runtime(payload, repo=tmp_path)


def test_admission_target_must_be_exact_registry_hypothesis_port(
    tmp_path: Path,
) -> None:
    payload = _runtime_search_fixture(tmp_path, admission=True)
    payload["admission"]["target_declaration"] = "Q3.RouteB.unrelatedTarget"
    with pytest.raises(
        supplier_preflight.SearchIntentError, match="BLOB_OR_PORT_DRIFT"
    ):
        supplier_preflight.validate_search_intent_runtime(payload, repo=tmp_path)


def test_admission_blocks_when_registry_has_no_distinct_consumer_challenge(
    tmp_path: Path,
) -> None:
    payload = _runtime_search_fixture(tmp_path, admission=True)
    registry_path = tmp_path / "orchestrator/state/NODE_REGISTRY_V10.json"
    registry = json.loads(registry_path.read_text(encoding="utf-8"))
    del registry["edges"][0]["hypothesis_port"]["challenge_declaration"]
    del registry["edges"][0]["hypothesis_port"]["challenge_type_sha256"]
    registry_path.write_text(json.dumps(registry), encoding="utf-8")
    with pytest.raises(
        supplier_preflight.SearchIntentError,
        match="CONSUMER_HYPOTHESIS_CHALLENGE_UNAVAILABLE",
    ):
        supplier_preflight.validate_search_intent_runtime(payload, repo=tmp_path)


def test_search_intent_runtime_rejects_symlinked_goal(tmp_path: Path) -> None:
    payload = _runtime_search_fixture(tmp_path, admission=False)
    goal = tmp_path / str(payload["goal_file"])
    real = goal.with_name("real.goal.md")
    goal.rename(real)
    goal.symlink_to(real.name)
    payload["goal_sha256"] = hashlib.sha256(real.read_bytes()).hexdigest()
    with pytest.raises(supplier_preflight.SearchIntentError, match="SYMLINK"):
        supplier_preflight.validate_search_intent_runtime(payload, repo=tmp_path)


def test_query_family_is_deterministic_bounded_and_semantic() -> None:
    intent = supplier_preflight.validate_search_intent(search_intent())
    intent["alias_hypotheses"].append(
        {
            "kind": "NEGATIVE",
            "term": "failure of compact convergence",
            "language": "en",
            "provenance": "counterexample card",
            "preserves": ["object", "output"],
        }
    )
    first = supplier_preflight.generate_search_queries(intent)
    second = supplier_preflight.generate_search_queries(intent)
    assert first == second
    assert 3 <= len(first) <= 5
    assert len({row["query"].casefold() for row in first}) == len(first)
    assert all(len(row["query"]) <= supplier_preflight.MAX_QUERY_CHARS for row in first)
    assert any(row["kind"] == "UNVERIFIED_CHARACTERIZATION_TRANSLATION" for row in first)
    assert any(row["kind"] == "UNVERIFIED_REPRESENTATION_DUAL" for row in first)
    assert any(row["kind"] == "NEGATIVE_OR_COUNTEREXAMPLE" for row in first)


def test_local_exact_fit_rejects_elaborated_target_identity_substitution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fit_module = fake_fit(resolved=True, fit_status="EXACT_FIT")
    fit_module.direct_type_fit = lambda candidate, _target: {
        "status": "EXACT_FIT",
        "candidate": {"name": candidate},
        "target": {"name": "Q3.RouteB.unrelatedTarget"},
    }
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fit_module)
    result = supplier_preflight._local_exact_fit(
        supplier_preflight.validate_search_intent(search_intent(mode="ADMISSION"))
    )
    assert result == {
        "status": "INCOMPLETE",
        "reason": "ADMISSION_ELABORATED_COMPARISON_IDENTITY_MISMATCH",
    }


def test_consumer_challenge_rejects_supplier_even_when_self_fit_would_pass(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fit_module = fake_fit(resolved=True)
    fit_module.direct_type_fit = lambda candidate, target: {
        "status": "EXACT_FIT" if candidate == target else "REJECTED",
        "candidate": {"name": candidate},
        "target": {"name": target},
    }
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fit_module)
    intent = supplier_preflight.validate_search_intent(search_intent(mode="ADMISSION"))
    result = supplier_preflight._local_exact_fit(intent)
    assert intent["admission"]["theorem"] != intent["admission"]["target_declaration"]
    assert result["status"] == "REJECTED"


def test_admission_exact_fit_stops_after_one_local_ask(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(supplier_preflight, "_run_local_ask", lambda query, **_kwargs: {"provider": "ask-local-cascade", "query": query, "status": "HITS", "errors": []})
    monkeypatch.setattr(supplier_preflight, "_local_exact_fit", lambda _intent: {"status": "EXACT_FIT", "comparison": {"status": "EXACT_FIT"}})
    monkeypatch.setattr(supplier_preflight, "_run_qmd", lambda *_args, **_kwargs: (_ for _ in ()).throw(AssertionError("qmd must not run")))
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: (_ for _ in ()).throw(AssertionError("external tools must not run")))
    result = supplier_preflight.run_search_intent(search_intent(mode="ADMISSION"))
    assert result["decision"] == "EXACT_FIT"
    assert result["metrics"]["qmd_subprocesses"] == 0
    assert result["metrics"]["external_lean_batches"] == 0


def test_discovery_caps_fanout_batches_and_tags_false_friends(monkeypatch: pytest.MonkeyPatch) -> None:
    qmd_calls: list[tuple[str, str]] = []
    external_calls: list[list[str]] = []
    web_calls: list[list[str]] = []
    monkeypatch.setattr(supplier_preflight, "_run_local_ask", lambda query, **_kwargs: {"provider": "ask-local-cascade", "query": query, "status": "HITS", "errors": []})
    monkeypatch.setattr(supplier_preflight, "_knowledge_aliases", lambda _anchors: [])

    def qmd(query: str, collection: str, **_kwargs: object) -> dict[str, object]:
        qmd_calls.append((collection, query))
        return {"provider": collection, "query": query, "status": "CANDIDATES", "errors": [], "candidates": [{"provider": collection, "provider_id": f"{collection}:{len(qmd_calls)}", "title": "generic compactness ground packet", "excerpt": "real line locally uniform convergence", "url": "local", "metadata_sha256": str(len(qmd_calls)) * 64}]}

    class Literature:
        @staticmethod
        def discover(queries: list[str]) -> dict[str, object]:
            web_calls.append(queries)
            return {"schema": "q3_literature_discovery.v1", "status": "ZERO_HITS_AT_TIME", "candidates": [], "errors": []}

        @staticmethod
        def validate_receipt(*_args: object, **_kwargs: object) -> tuple[bool, list[str]]:
            return True, []

    class External:
        @staticmethod
        def search_registry_batch(queries: list[str], **_kwargs: object) -> dict[str, object]:
            external_calls.append(queries)
            return {"schema": "q3_external_lean_search.v3", "queries": [{"query": query, "matches": []} for query in queries], "errors": []}

        @staticmethod
        def validate_batch_receipt(_payload: object, **_kwargs: object) -> tuple[bool, list[str]]:
            return True, []

    monkeypatch.setattr(supplier_preflight, "_run_qmd", qmd)
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda name, _path: Literature if "literature" in name else External)
    result = supplier_preflight.run_search_intent(search_intent(network="ALLOW_FREE_METADATA"))
    assert len(qmd_calls) <= 8
    assert len(set(qmd_calls)) == len(qmd_calls)
    assert len(external_calls) == 1
    assert len(external_calls[0]) <= 8
    assert 1 <= len(web_calls) <= 2
    assert any(row["classification"] == "KNOWN_FALSE_FRIEND" for row in result["candidates"])


def test_ask_covered_pair_is_not_requeried_and_candidates_are_preserved(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[tuple[str, str]] = []
    planted = search_intent()
    planted["collections"] = ["q3_docs", "math_papers", "zotero_lib"]
    canonical = supplier_preflight.generate_search_queries(planted)[0]["query"]
    monkeypatch.setattr(
        supplier_preflight,
        "_run_local_ask",
        lambda query, **_kwargs: {
            "provider": "ask-local-cascade",
            "query": query,
            "status": "HITS",
            "errors": [],
            "provider_rows": [{"provider": "q3_docs", "query": query}],
            "candidates": [{
                "provider": "q3_docs", "provider_id": "ask-hit",
                "title": "ground packet compact convergence", "excerpt": "real line",
                "url": "local", "metadata_sha256": "a" * 64,
            }],
        },
    )

    def qmd(query: str, collection: str, **_kwargs: object) -> dict[str, object]:
        calls.append((collection, query))
        return {
            "provider": collection, "query": query,
            "status": "LOCAL_ZERO_AT_CORPUS_HASH", "errors": [], "candidates": [],
        }

    monkeypatch.setattr(supplier_preflight, "_run_qmd", qmd)
    monkeypatch.setattr(supplier_preflight, "_knowledge_aliases", lambda _terms: [])

    class External:
        @staticmethod
        def search_registry_batch(queries: list[str], **_kwargs: object) -> dict[str, object]:
            return {"schema": "q3_external_lean_search.v3", "queries": [], "errors": []}

        @staticmethod
        def validate_batch_receipt(*_args: object, **_kwargs: object) -> tuple[bool, list[str]]:
            return True, []

    monkeypatch.setattr(supplier_preflight, "_load_module", lambda _name, _path: External)
    result = supplier_preflight.run_search_intent(planted)
    assert ("q3_docs", canonical) not in calls
    assert len(calls) <= 8
    assert any(row["provider_id"] == "ask-hit" for row in result["candidates"])
    assert result["status"] == "PASS"


def test_local_ask_receipt_preserves_bound_candidate_rows(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    query = "ground packet"
    query_sha256 = hashlib.sha256(query.encode()).hexdigest()
    candidate = {
        "provider": "q3_docs",
        "query": query,
        "query_sha256": query_sha256,
        "provider_id": "doc-1",
        "title": "ground packet",
        "excerpt": "compact convergence",
        "url": "local",
        "corpus_sha256": "c" * 64,
        "collection_identity": "d" * 64,
    }
    candidate["metadata_sha256"] = supplier_preflight._canonical_hash(candidate)
    receipt = {
        "schema": "q3_ask_local_receipt.v1",
        "query": query,
        "query_sha256": query_sha256,
        "provider_rows": [
            {
                "provider": "local-shelves", "query": query,
                "query_sha256": query_sha256, "status": "HITS",
            },
                {
                    "provider": "q3_docs", "query": query,
                    "query_sha256": query_sha256, "status": "CANDIDATES",
                    "corpus_sha256": "c" * 64,
                    "collection_identity": "d" * 64,
                    "candidate_count": 1,
                    "candidate_hashes": [candidate["metadata_sha256"]],
                },
        ],
        "candidate_rows": [candidate],
        "external_lean": "DEFERRED",
        "boundary": "LOCAL_RECEIPT_FOREIGN_INCOMPLETE",
    }
    stdout = "ASK_RECEIPT_JSON: " + json.dumps(receipt) + "\n"
    monkeypatch.setattr(
        supplier_preflight.subprocess,
        "run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess(
            args=[], returncode=0, stdout=stdout, stderr=""
        ),
    )
    result = supplier_preflight._run_local_ask(query, timeout=1)
    assert result["errors"] == []
    assert result["candidates"] == [candidate]


def test_local_ask_stale_q3_docs_identity_cannot_contribute_candidate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    query = "ground packet"
    query_sha256 = hashlib.sha256(query.encode()).hexdigest()
    candidate = {
        "provider": "q3_docs",
        "query": query,
        "query_sha256": query_sha256,
        "provider_id": "doc-1",
        "title": "ground packet",
        "excerpt": "compact convergence",
        "url": "local",
        "corpus_sha256": "c" * 64,
        "collection_identity": "d" * 64,
    }
    candidate["metadata_sha256"] = supplier_preflight._canonical_hash(candidate)
    receipt = {
        "schema": "q3_ask_local_receipt.v1",
        "query": query,
        "query_sha256": query_sha256,
        "provider_rows": [
            {
                "provider": "local-shelves",
                "query": query,
                "query_sha256": query_sha256,
                "status": "HITS",
            },
            {
                "provider": "q3_docs",
                "query": query,
                "query_sha256": query_sha256,
                "status": "CANDIDATES",
                "corpus_sha256": "e" * 64,
                "collection_identity": "d" * 64,
                "candidate_count": 1,
                "candidate_hashes": [candidate["metadata_sha256"]],
            },
        ],
        "candidate_rows": [candidate],
        "external_lean": "DEFERRED",
        "boundary": "LOCAL_RECEIPT_FOREIGN_INCOMPLETE",
    }
    monkeypatch.setattr(
        supplier_preflight.subprocess,
        "run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess(
            args=[], returncode=0, stdout="ASK_RECEIPT_JSON: " + json.dumps(receipt), stderr=""
        ),
    )
    result = supplier_preflight._run_local_ask(query, timeout=1)
    assert "ASK_LOCAL_Q3_DOCS_IDENTITY_INVALID" in result["errors"]
    assert result["candidates"] == []


def test_conditional_network_waits_for_complete_local_denominator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    web_calls: list[list[str]] = []
    planted = search_intent(network="AFTER_LOCAL_COMPLETE_NO_EXACT_FIT")
    monkeypatch.setattr(
        supplier_preflight,
        "_run_local_ask",
        lambda query, **_kwargs: {
            "provider": "ask-local-cascade", "query": query,
            "status": "INCOMPLETE", "errors": ["local failure"],
        },
    )
    monkeypatch.setattr(
        supplier_preflight,
        "_run_qmd",
        lambda query, collection, **_kwargs: {
            "provider": collection, "query": query, "errors": [], "candidates": []
        },
    )

    class Literature:
        @staticmethod
        def discover(queries: list[str]) -> dict[str, object]:
            web_calls.append(queries)
            return {"schema": "q3_literature_discovery.v1", "status": "ZERO_HITS_AT_TIME", "candidates": [], "errors": []}

        @staticmethod
        def validate_receipt(*_args: object, **_kwargs: object) -> tuple[bool, list[str]]:
            return True, []

    class External:
        @staticmethod
        def search_registry_batch(*_args: object, **_kwargs: object) -> dict[str, object]:
            return {"queries": [], "errors": []}

        @staticmethod
        def validate_batch_receipt(*_args: object, **_kwargs: object) -> tuple[bool, list[str]]:
            return True, []

    monkeypatch.setattr(supplier_preflight, "_load_module", lambda name, _path: Literature if "literature" in name else External)
    result = supplier_preflight.run_search_intent(planted)
    assert web_calls == []
    assert result["status"] == "INCOMPLETE"


def test_external_batch_scans_each_root_once(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    root = tmp_path / "base"
    root.mkdir()
    (root / "Sample.lean").write_text("theorem compactGround : True := by trivial\n", encoding="utf-8")
    calls = 0
    real = search_external_lean._scan_base_batch

    def counted(*args: object, **kwargs: object):
        nonlocal calls
        calls += 1
        return real(*args, **kwargs)

    monkeypatch.setattr(search_external_lean, "_scan_base_batch", counted)
    payload = search_external_lean.search_registry_batch(
        ["compactGround", "ground compact"], bases=[("sample", root)], enabled_ids=["sample"], budget_seconds=5,
    )
    valid, errors = search_external_lean.validate_batch_receipt(payload, expected_queries=["compactGround", "ground compact"])
    assert calls == 1
    assert payload["base_results"][0]["identity_final"] == payload["base_results"][0]["identity_after"]
    assert valid, errors


def test_external_batch_final_global_identity_replay_detects_late_mutation(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    root = tmp_path / "base"
    root.mkdir()
    source = root / "Sample.lean"
    source.write_text("theorem sample : True := by trivial\n", encoding="utf-8")
    real = search_external_lean._content_identity
    calls = 0

    def mutate_before_final(path: Path, deadline: float):
        nonlocal calls
        calls += 1
        if calls == 3:
            source.write_text("theorem sample : True := by exact True.intro\n", encoding="utf-8")
        return real(path, deadline)

    monkeypatch.setattr(search_external_lean, "_content_identity", mutate_before_final)
    payload = search_external_lean.search_registry_batch(
        ["sample"], bases=[("sample", root)], enabled_ids=["sample"], budget_seconds=5
    )
    assert any("changed after batch scan" in error for error in payload["errors"])
    valid, _ = search_external_lean.validate_batch_receipt(
        payload, expected_queries=["sample"]
    )
    assert not valid


def test_external_query_terms_preserve_mixed_unicode_scripts() -> None:
    assert search_external_lean.query_terms("compact сходимость пакет") == [
        "compact",
        "сходимость",
        "пакет",
    ]


def test_external_batch_rejects_two_ids_for_one_physical_corpus(
    tmp_path: Path,
) -> None:
    (tmp_path / "Sample.lean").write_text(
        "theorem sample : True := by trivial\n", encoding="utf-8"
    )
    payload = search_external_lean.search_registry_batch(
        ["sample theorem"],
        bases=[("left", tmp_path), ("right", tmp_path)],
        enabled_ids=["left", "right"],
        budget_seconds=1,
    )
    assert any("duplicate canonical corpus root" in error for error in payload["errors"])
    assert payload["base_results"] == []


def test_literature_response_overflow_is_incomplete(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(literature_discovery, "_fetch", lambda *_args, **_kwargs: (_ for _ in ()).throw(literature_discovery.DiscoveryIncomplete("HTTP response exceeds 524288 bytes")))
    result = literature_discovery.discover(["ground packet"], providers=("arxiv",), timeout_seconds=1)
    assert result["status"] == "INCOMPLETE"
    assert result["provider_rows"][0]["status"] == "INCOMPLETE"


def test_literature_zero_is_time_bound_not_absence(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(literature_discovery, "_arxiv", lambda *_args, **_kwargs: [])
    result = literature_discovery.discover(["ground packet"], providers=("arxiv",), timeout_seconds=1)
    assert result["status"] == "ZERO_HITS_AT_TIME"
    assert result["provider_rows"][0]["status"] == "ZERO_HITS_AT_TIME"


def test_literature_duplicate_hit_is_not_reported_as_zero(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    row = {
        "provider": "arxiv",
        "provider_id": "same",
        "title": "same",
        "excerpt": "",
        "url": "u",
        "published": "2026",
        "metadata_sha256": "a" * 64,
    }
    monkeypatch.setattr(
        literature_discovery, "_arxiv", lambda *_args, **_kwargs: [row]
    )
    result = literature_discovery.discover(
        ["first", "second"], providers=("arxiv",), timeout_seconds=1
    )
    assert result["provider_rows"][0]["status"] == "CANDIDATES"
    assert result["provider_rows"][1]["status"] == "HITS_DEDUPED"


def test_literature_batch_has_one_monotonic_deadline(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def slow(*_args: object, **_kwargs: object) -> list[dict[str, object]]:
        time.sleep(0.2)
        return []

    monkeypatch.setattr(literature_discovery, "_arxiv", slow)
    started = time.monotonic()
    result = literature_discovery.discover(
        ["first", "second"], providers=("arxiv",), timeout_seconds=0.03
    )
    elapsed = time.monotonic() - started
    assert elapsed < 0.15
    assert result["status"] == "INCOMPLETE"
    assert all(row["status"] == "INCOMPLETE" for row in result["provider_rows"])


def test_literature_validator_rejects_row_top_error_status_incoherence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(literature_discovery, "_arxiv", lambda *_args, **_kwargs: [])
    payload = literature_discovery.discover(
        ["ground packet"], providers=("arxiv",), timeout_seconds=1
    )
    valid, errors = literature_discovery.validate_receipt(
        payload, expected_queries=["ground packet"], expected_providers=("arxiv",)
    )
    assert valid, errors
    planted = json.loads(json.dumps(payload))
    planted["provider_rows"][0]["errors"] = ["planted failure"]
    planted["provider_rows"][0]["status"] = "INCOMPLETE"
    valid, errors = literature_discovery.validate_receipt(
        planted, expected_queries=["ground packet"], expected_providers=("arxiv",)
    )
    assert not valid
    assert "LITERATURE_RECEIPT_ERROR_LEDGER_INVALID" in errors


def test_stdout_budget_compaction_is_explicitly_incomplete() -> None:
    payload = {
        "schema": "q3_search_evidence.v1",
        "status": "PASS",
        "decision": "CANDIDATES",
        "errors": [],
        "provider_ledger": [],
        "candidates": [
            {"provider": "q3_docs", "provider_id": str(index), "excerpt": "x" * 1200}
            for index in range(24)
        ],
        "literature": [{"payload": "y" * 20000}],
        "external_lean": {"payload": "z" * 20000},
    }
    rendered = supplier_preflight.bounded_evidence_json(payload)
    decoded = json.loads(rendered)
    assert len(rendered.encode("utf-8")) <= supplier_preflight.STDOUT_MAX_BYTES
    assert decoded["status"] == "INCOMPLETE"
    assert "STDOUT_BUDGET_COMPACTION" in decoded["errors"]


def test_external_process_receipt_is_bound_to_exact_request(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = {
        "schema": supplier_preflight.EXTERNAL_SCHEMA,
        "query": "different query",
        "query_sha256": "0" * 64,
        "candidate": "Q3.wrong",
        "candidate_sha256": "0" * 64,
        "candidate_provenance": "SOURCE_DECLARED",
        "budget_seconds": 15,
        "enabled_bases": [],
        "bases_queried": [],
        "base_results": [],
        "matches": [],
        "terms": ["different"],
        "registry_sha256": "0" * 64,
        "errors": [],
        "boundary": "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE",
    }
    monkeypatch.setattr(
        supplier_preflight.subprocess,
        "run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess(
            args=[], returncode=0, stdout=json.dumps(payload), stderr=""
        ),
    )
    result = supplier_preflight.run_external(
        "exact query",
        candidate="Q3.expected",
        candidate_provenance="SOURCE_DECLARED",
    )
    assert result["error"] is not None
    assert "receipt invalid" in str(result["error"])


def test_ask_shelf_preserves_utf8_when_truncating_long_lean_matches() -> None:
    proc = subprocess.run(
        [
            str(supplier_preflight.ASK),
            "selectedFerrersPreAnchorIndex N less than "
            "sourceWeilEvenTailCutoff W02 norm lower bound",
        ],
        cwd=supplier_preflight.REPO,
        capture_output=True,
        text=False,
        check=False,
    )
    assert proc.returncode in {0, 1, 2}
    proc.stdout.decode("utf-8")
    proc.stderr.decode("utf-8")


def record(name: str, module: str = "Q3.Proofs.RouteB.Sample") -> dict[str, object]:
    return {
        "name": name,
        "kind": "theorem",
        "type": "True",
        "levelParams": [],
        "numBinders": 0,
        "file": module,
        "line": "1",
        "doc": "",
        "typeConsts": [],
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
        "isPrivate": False,
        "isUnsafe": False,
    }


def test_resolve_declaration_accepts_full_name_and_unique_basename() -> None:
    index = {"Q3.RouteB.exact": record("Q3.RouteB.exact")}
    assert fit.resolve_declaration("Q3.RouteB.exact", index)[0] == "Q3.RouteB.exact"
    assert fit.resolve_declaration("exact", index)[0] == "Q3.RouteB.exact"


def test_resolve_declaration_rejects_ambiguous_basename() -> None:
    index = {
        "Q3.RouteB.Left.same": record("Q3.RouteB.Left.same"),
        "Q3.RouteB.Right.same": record("Q3.RouteB.Right.same"),
    }
    with pytest.raises(fit.FitError, match="DECLARATION_AMBIGUOUS"):
        fit.resolve_declaration("same", index)


def test_resolve_declaration_never_substitutes_a_qualified_name() -> None:
    index = {"Other.Namespace.same": record("Other.Namespace.same")}
    with pytest.raises(fit.FitError, match="DECLARATION_NOT_FOUND"):
        fit.resolve_declaration("Expected.Namespace.same", index)


def test_harness_uses_target_term_type_and_both_modules() -> None:
    candidate = record("Q3.RouteB.supplier", "Q3.Proofs.RouteB.Supplier")
    target = record("Q3.RouteB.target", "Q3.Proofs.RouteB.Target")
    target["type"] = "∀ n : Nat, n = n"
    source = fit._harness_source(
        "Q3.RouteB.supplier", candidate, "Q3.RouteB.target", target
    )
    assert "import Q3.Proofs.RouteB.Supplier" in source
    assert "import Q3.Proofs.RouteB.Target" in source
    assert "q3ComparatorExpectedType _ (@Q3.RouteB.target)" in source
    assert "exact (@Q3.RouteB.supplier)" in source
    assert str(target["type"]) not in source


def external_payload(
    *,
    exact: str = "ABSENT",
    query: str = "supplier",
    candidate: str | None = None,
    candidate_provenance: str | None = None,
) -> dict[str, object]:
    boundary = (
        supplier_preflight.SOURCE_ABSENCE_SCOPE
        if exact == "ABSENT"
        else "SOURCE_DECLARATION_PRESENT"
    )
    return {
        "schema": supplier_preflight.EXTERNAL_SCHEMA,
        "query": query,
        "query_sha256": __import__("hashlib").sha256(query.encode()).hexdigest(),
        "candidate": candidate,
        "candidate_sha256": (
            __import__("hashlib").sha256(candidate.encode()).hexdigest()
            if candidate is not None
            else None
        ),
        "candidate_provenance": candidate_provenance,
        "enabled_bases": ["zeta23"],
        "bases_queried": ["zeta23"],
        "matches": [],
        "errors": [],
        "boundary": "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE",
        "base_results": [
            {
                "base_id": "zeta23",
                "exact_candidate": {
                    "status": exact,
                    "boundary": boundary,
                    "searched_regular_source_count": 12,
                },
            }
        ],
    }


def external_run(
    *,
    exact: str = "ABSENT",
    query: str = "supplier",
    candidate: str | None = None,
    candidate_provenance: str | None = None,
) -> dict[str, object]:
    payload = external_payload(
        exact=exact,
        query=query,
        candidate=candidate,
        candidate_provenance=candidate_provenance,
    )
    return {
        "returncode": 0,
        "stdout": __import__("json").dumps(payload),
        "stderr": "",
        "duration_ms": 1,
        "payload": payload,
        "error": None,
    }


def patch_retrieval(
    monkeypatch: pytest.MonkeyPatch, *, shelf: str = "HITS", exact: str = "ABSENT"
) -> None:
    monkeypatch.setattr(
        supplier_preflight,
        "run_external",
        lambda query, **kwargs: external_run(
            exact=exact,
            query=query,
            candidate=kwargs.get("candidate"),
            candidate_provenance=kwargs.get("candidate_provenance"),
        ),
    )
    monkeypatch.setattr(
        supplier_preflight,
        "run_shelf",
        lambda _query, **_kwargs: {
            "status": shelf,
            "returncode": {"HITS": 0, "SHELF_ABSENCE": 1, "INCOMPLETE": 2}[shelf],
        },
    )


def fake_fit(
    *, freshness: str = "PASS", resolved: bool = False, fit_status: str = "EXACT_FIT"
) -> SimpleNamespace:
    class FakeFitError(ValueError):
        code = "DECLARATION_NOT_FOUND"

    def resolve(name: str, _index: object) -> object:
        if not resolved:
            raise FakeFitError("DECLARATION_NOT_FOUND")
        return name, record(name)

    return SimpleNamespace(
        FitError=FakeFitError,
        environment_freshness=lambda: {
            "status": freshness,
            "refresh_command": fit.ENVDUMP_COMMAND if freshness != "PASS" else None,
        },
        load_index=lambda: {},
        resolve_declaration=resolve,
        source_declaration_candidates=lambda _name: [],
        declaration_properties=lambda name, row: {"name": name, **row},
        direct_type_fit=lambda candidate, target: {
            "status": fit_status,
            "candidate": {"name": candidate},
            "target": {"name": target},
        },
    )


def test_stale_environment_is_incomplete_and_prints_exact_command(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    monkeypatch.setattr(
        supplier_preflight,
        "_load_module",
        lambda *_args: fake_fit(freshness="INCOMPLETE"),
    )
    result = supplier_preflight.run_preflight("supplier", candidate="candidate")
    assert result["status"] == "INCOMPLETE"
    assert result["environment"]["refresh_command"] == fit.ENVDUMP_COMMAND


def test_foreign_exact_declaration_is_not_claimed_as_local_fit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch, exact="PRESENT")
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fake_fit())
    result = supplier_preflight.run_preflight(
        "xiPrime_zeros_in_open_critical_strip",
        candidate="xiPrime_zeros_in_open_critical_strip",
    )
    assert result["status"] == "FOREIGN_UNVERIFIED"


def test_query_only_shelf_absence_requires_precise_candidate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch, shelf="SHELF_ABSENCE")
    result = supplier_preflight.run_preflight("guaranteed_missing_declaration_xyz")
    assert result["status"] == "INCOMPLETE"
    assert result["reason"] == "PRECISE_CANDIDATE_REQUIRED_FOR_COMPLETE_ABSENCE"


def test_exact_declaration_absence_ignores_prose_only_candidates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fake_fit())
    result = supplier_preflight.run_preflight(
        "guaranteed_missing_declaration_xyz",
        candidate="guaranteed_missing_declaration_xyz",
        candidate_provenance="SOURCE_DECLARED",
    )
    assert result["status"] == "COMPLETE_ABSENCE"
    assert result["prose_candidates_present"] is True
    assert result["source_absence_scope"] == "SOURCE_DECLARATION_ABSENCE"


def test_source_only_q3_or_mathlib_declaration_remains_candidate_only(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    fit_module = fake_fit()
    fit_module.source_declaration_candidates = lambda _name: [
        {"source": "mathlib", "file": "Mathlib/Example.lean", "line": 1}
    ]
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fit_module)
    result = supplier_preflight.run_preflight("Mathlib.example", candidate="Mathlib.example")
    assert result["status"] == "CANDIDATE_ONLY"
    assert result["source_candidates"][0]["source"] == "mathlib"


def test_generated_candidate_miss_never_claims_source_absence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch, shelf="SHELF_ABSENCE")
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fake_fit())
    result = supplier_preflight.run_preflight(
        "missing projection",
        candidate="Q3.missingProjection",
        candidate_provenance="GENERATED_OR_DERIVED",
    )
    assert result["status"] == "INCOMPLETE"
    assert result["reason"] == "ELABORATED_EXTERNAL_DECLARATION_LOOKUP_REQUIRED"
    assert result["source_absence_scope"] is None


def test_exact_fit_is_preserved_only_from_direct_comparator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    monkeypatch.setattr(
        supplier_preflight,
        "_load_module",
        lambda *_args: fake_fit(resolved=True, fit_status="EXACT_FIT"),
    )
    result = supplier_preflight.run_preflight(
        "supplier",
        candidate="Q3.RouteB.supplier",
        target="Q3.RouteB.target",
        candidate_provenance="SOURCE_DECLARED",
    )
    assert result["status"] == "EXACT_FIT"
    assert result["comparison"]["status"] == "EXACT_FIT"
    assert result["comparison"]["candidate"]["name"] == "Q3.RouteB.supplier"
    assert result["comparison"]["target"]["name"] == "Q3.RouteB.target"


def test_generated_candidate_requires_verifiable_provenance_evidence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    monkeypatch.setattr(
        supplier_preflight,
        "_load_module",
        lambda *_args: fake_fit(resolved=True, fit_status="EXACT_FIT"),
    )
    result = supplier_preflight.run_preflight(
        "supplier",
        candidate="Q3.RouteB.supplier",
        target="Q3.RouteB.target",
        candidate_provenance="GENERATED_OR_DERIVED",
    )
    assert result["status"] == "INCOMPLETE"
    assert result["reason"] == "CANDIDATE_PROVENANCE_EVIDENCE_REQUIRED"


def test_comparator_identity_substitution_cannot_be_exact_fit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    fit_module = fake_fit(resolved=True, fit_status="EXACT_FIT")
    fit_module.direct_type_fit = lambda _candidate, target: {
        "status": "EXACT_FIT",
        "candidate": {"name": "Other.Namespace.supplier"},
        "target": {"name": target},
    }
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fit_module)
    result = supplier_preflight.run_preflight(
        "supplier",
        candidate="Q3.RouteB.supplier",
        target="Q3.RouteB.target",
        candidate_provenance="SOURCE_DECLARED",
    )
    assert result["status"] == "INCOMPLETE"
    assert result["reason"] == "direct type-fit declaration identity mismatch"


def test_external_receipt_is_mode_0600_and_removed_after_shelf(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed: list[tuple[object, int]] = []
    monkeypatch.setattr(
        supplier_preflight,
        "run_external",
        lambda *_args, **_kwargs: external_run(),
    )

    def inspect_receipt(_query: str, *, external_receipt, **_kwargs):
        observed.append(
            (external_receipt, external_receipt.stat().st_mode & 0o777)
        )
        assert external_receipt.parent != supplier_preflight.REPO
        return {"status": "HITS", "returncode": 0}

    monkeypatch.setattr(supplier_preflight, "run_shelf", inspect_receipt)
    result = supplier_preflight.run_preflight("supplier")
    assert result["status"] == "CANDIDATE_ONLY"
    assert observed[0][1] == 0o600
    assert not observed[0][0].exists()


def test_receipt_is_removed_when_shelf_raises(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed = []
    monkeypatch.setattr(
        supplier_preflight,
        "run_external",
        lambda *_args, **_kwargs: external_run(),
    )

    def fail(_query: str, *, external_receipt, **_kwargs):
        observed.append(external_receipt)
        raise OSError("plant")

    monkeypatch.setattr(supplier_preflight, "run_shelf", fail)
    result = supplier_preflight.run_preflight("supplier")
    assert result["status"] == "INCOMPLETE"
    assert not observed[0].exists()


def test_external_receipt_candidate_binding_mismatch_is_incomplete(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    replay = external_run(
        query="supplier",
        candidate="Q3.replayed",
        candidate_provenance="SOURCE_DECLARED",
    )
    monkeypatch.setattr(
        supplier_preflight, "run_external", lambda *_args, **_kwargs: replay
    )
    monkeypatch.setattr(
        supplier_preflight,
        "run_shelf",
        lambda *_args, **_kwargs: {"status": "HITS", "returncode": 0},
    )
    result = supplier_preflight.run_preflight(
        "supplier",
        candidate="Q3.expected",
        candidate_provenance="SOURCE_DECLARED",
    )
    assert result["status"] == "INCOMPLETE"
    assert result["reason"] == "enabled external-base denominator failed"
