from __future__ import annotations

import copy
import fcntl
import json
from contextlib import nullcontext
from pathlib import Path

import pytest

from orchestrator import lean_dependency_runtime
from orchestrator import node_registry_v10 as registry

ROOT = Path(__file__).resolve().parents[2]
GOAL = "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md"


def rehash(document: dict) -> dict:
    edges = {edge["edge_id"]: edge for edge in document["edges"]}
    for node in document["nodes"]:
        node["validation_hash"] = registry._validation_digest(
            node["validation_inputs"],
            node["semantic_review_inputs"]["exact_edges"],
            edges,
        )
        node["semantic_review_hash"] = registry._semantic_review_digest(
            node["semantic_review_inputs"], edges
        )
        for evidence in node["review"]["evidence"]:
            evidence["exact_payload_hash"] = node["semantic_review_hash"]
    document["registry_hash"] = registry.digest(
        {key: value for key, value in document.items() if key != "registry_hash"}
    )
    return document


def expr_fingerprint(value: int) -> dict[str, str]:
    return {"algorithm": "LEAN_EXPR_HASH_V1", "value": str(value)}


def candidate_receipt(path: str, bytes_sha256: str) -> dict:
    candidate_set = [{"path": path, "sha256": bytes_sha256}]
    return {
        "command": [
            "lake",
            "env",
            "lean",
            path.removeprefix("q3.lean.aristotle/"),
        ],
        "returncode": 0,
        "stdout_sha256": "a" * 64,
        "stderr_sha256": "b" * 64,
        "path": path,
        "bytes_sha256": bytes_sha256,
        "candidate_set": candidate_set,
        "candidate_set_sha256": registry.digest(candidate_set),
    }


def assert_complete_validation_evidence(result: dict) -> None:
    evidence = result["validation_evidence"][0]
    assert set(evidence) >= {
        "toolchain",
        "modules",
        "theorem_ids",
        "actions",
        "holes",
        "theorem_axioms",
        "axiom_policy_sha256",
        "dependency_result",
        "project_source_baseline",
    }
    assert all(action["exit_code"] == 0 for action in evidence["actions"])


def live() -> dict:
    return registry._read_registry_document(ROOT)


def test_live_registry_has_seven_v9_nodes_nine_edges_and_three_unmapped() -> None:
    document = live()
    assert document["algorithm_version"] == registry.ALGORITHM_VERSION
    assert len(document["nodes"]) == 7
    assert len(document["edges"]) == 9
    assert sum(node["lifecycle"] == "HISTORICAL_V9_UNMAPPED" for node in document["nodes"]) == 3
    assert document["project"]["root_count"] == len(document["project"]["roots"]) == 1
    assert document["project"]["file_count"] == 3590
    assert document["project"]["project_dependency_tree_hash"] == (
        "12c3a49e41ef98f96438e00bee7327a3c6db6e7cad18d1feda5dbae96ed39160"
    )

    arch_prime = next(
        node
        for node in document["nodes"]
        if node["node_id"]
        == "GOAL058_D0PSTAR_SOURCE_ARCH_PRIME_EVEN_TAIL_FLOOR_20260901"
    )
    assert arch_prime["lifecycle"] == "HISTORICAL_V9_UNMAPPED"
    assert arch_prime["semantic_review_inputs"]["exact_edges"] == []
    assert arch_prime["terminal_consumer"] == []
    assert arch_prime["theorem_ids"] == [
        "Q3.RouteB.D0Pstar."
        "sourceArchPrimeSesquilinearForm_re_self_lower_evenGraphFinsuppShift"
    ]
    assert arch_prime["review"]["historical_receipt"]["entry_id"] == (
        arch_prime["node_id"]
    )


def test_authority_loader_requires_clean_exact_head_bytes(monkeypatch) -> None:
    raw = (ROOT / registry.DEFAULT_PATH).read_bytes()
    expected_hash = registry._parse_registry_bytes(raw)["registry_hash"]
    monkeypatch.setattr(registry, "_path_has_symlink", lambda repo, path: False)
    monkeypatch.setattr(registry, "_dirty_paths", lambda repo, paths: {registry.DEFAULT_PATH})
    with pytest.raises(registry.NodeRegistryError, match="AUTHORITY_DIRTY"):
        registry.load_registry(ROOT)

    monkeypatch.setattr(registry, "_dirty_paths", lambda repo, paths: set())
    monkeypatch.setattr(registry, "_git_bytes", lambda repo, *args: raw + b" ")
    with pytest.raises(registry.NodeRegistryError, match="AUTHORITY_HEAD_BLOB_DRIFT"):
        registry.load_registry(ROOT)

    monkeypatch.setattr(registry, "_git_bytes", lambda repo, *args: raw)
    monkeypatch.setattr(
        registry,
        "_read_registry_document",
        lambda *args, **kwargs: (_ for _ in ()).throw(
            AssertionError("authority loader reread registry after byte comparison")
        ),
    )
    assert registry.load_registry(ROOT)["registry_hash"] == expected_hash


def test_zero_git_structural_reader_rejects_symlink_and_outside_repo(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    outside = tmp_path / "outside"
    (repo / "orchestrator").mkdir(parents=True)
    outside.mkdir()
    registry_copy = outside / "NODE_REGISTRY_V10.json"
    registry_copy.write_bytes((ROOT / registry.DEFAULT_PATH).read_bytes())
    (repo / "orchestrator/state").symlink_to(outside, target_is_directory=True)
    with pytest.raises(registry.NodeRegistryError, match="STRUCTURAL_SYMLINK_FORBIDDEN"):
        registry._read_registry_document(repo)
    with pytest.raises(registry.NodeRegistryError, match="STRUCTURAL_PATH_OUTSIDE_REPO"):
        registry._read_registry_document(repo, registry_copy)


def test_registry_paths_reject_lexical_parent_segments(tmp_path: Path, monkeypatch) -> None:
    repo = tmp_path / "repo"
    (repo / "orchestrator/state").mkdir(parents=True)
    (repo / registry.DEFAULT_PATH).write_bytes((ROOT / registry.DEFAULT_PATH).read_bytes())
    lexical = "orchestrator/state/../state/NODE_REGISTRY_V10.json"
    with pytest.raises(registry.NodeRegistryError, match="PATH_INVALID"):
        registry._read_registry_document(repo, lexical)
    monkeypatch.setattr(registry, "_dirty_paths", lambda repo, paths: set())
    with pytest.raises(registry.NodeRegistryError, match="PATH_INVALID"):
        registry.load_registry(repo, lexical)


def test_nested_toolchain_path_traversal_and_malformed_types_fail_closed() -> None:
    document = live()
    document["nodes"][0]["validation_inputs"]["toolchain"]["path"] = (
        "q3.lean.aristotle/../outside-toolchain"
    )
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="PATH_INVALID"):
        registry._validate_registry(document)

    document = live()
    document["nodes"][0]["semantic_review_inputs"]["definitions"] = 7
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="DEFINITIONS_INVALID"):
        registry._validate_registry(document)


def test_project_dependency_pin_is_cross_bound_to_every_node() -> None:
    document = live()
    document["nodes"][0]["validation_inputs"]["dependency_graph"][
        "project_dependency_tree_hash"
    ] = "0" * 64
    rehash(document)
    with pytest.raises(
        registry.NodeRegistryError, match="PROJECT_DEPENDENCY_BINDING_DRIFT"
    ):
        registry._validate_registry(document)


def test_physical_goal_binding_accepts_any_canonical_bus_goal_only() -> None:
    document = live()
    node = document["nodes"][0]
    future_goal = "docs/routeB_bus/999AB_future-goal.goal.md"
    node["validation_inputs"]["physical_goal_path"] = future_goal
    rehash(document)
    registry._validate_registry(document)
    scoped, edge_ids, scope_kind = registry._resolve_scope(document, future_goal)
    assert [row["node_id"] for row in scoped] == [node["node_id"]]
    assert edge_ids == set(node["semantic_review_inputs"]["exact_edges"])
    assert scope_kind == "PHYSICAL_GOAL"

    for invalid in (
        "docs/Codex/999_future.goal.md",
        "docs/routeB_bus/nested/999_future.goal.md",
        "docs/routeB_bus/999_future.md",
    ):
        malformed = live()
        malformed["nodes"][0]["validation_inputs"]["physical_goal_path"] = invalid
        rehash(malformed)
        with pytest.raises(
            registry.NodeRegistryError, match="PHYSICAL_GOAL_BINDING_INVALID"
        ):
            registry._validate_registry(malformed)


def test_malformed_registry_startup_returns_structured_fatal(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    registry_path = repo / registry.DEFAULT_PATH
    registry_path.parent.mkdir(parents=True)
    document = live()
    document["edges"] = 7
    registry_path.write_text(json.dumps(document), encoding="utf-8")
    result = registry.startup_gate_summary(repo, None)
    assert result["status"] == "FATAL"
    assert "NODE_REGISTRY_SCHEMA_INVALID" in result["detail"]


def test_runtime_source_closure_batches_head_blob_lookup(
    tmp_path: Path, monkeypatch
) -> None:
    source_paths = [
        "q3.lean.aristotle/Q3/A.lean",
        "q3.lean.aristotle/Q3/B.lean",
    ]
    fingerprints = []
    for index, rel in enumerate(source_paths):
        path = tmp_path / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"theorem t{index} : True := by trivial\n", encoding="utf-8")
        fingerprints.append({"path": rel, "sha256": registry._file_sha256(path)})
    calls: list[tuple[str, ...]] = []

    def fake_git_bytes(repo: Path, *args: str) -> bytes:
        calls.append(args)
        return b"".join(
            f"100644 blob {'a' * 39}{index}\t{rel}\0".encode()
            for index, rel in enumerate(source_paths)
        )

    monkeypatch.setattr(registry, "_git_bytes", fake_git_bytes)
    monkeypatch.setattr(registry, "_path_has_symlink", lambda repo, path: False)
    root_paths = [source_paths[0]]
    evidence = {
        "source_paths": source_paths,
        "source_fingerprints": fingerprints,
        "root_source_paths": root_paths,
        "prebuild_root_source_fingerprints": fingerprints[:1],
        "project_source_baseline": {
            "root_path": "q3.lean.aristotle/Q3",
            "file_count": 2,
            "algorithm": "PATH_TAB_CONTENT_SHA256_NEWLINE_V1",
            "tree_sha256": "b" * 64,
        },
        "source_map_sha256": registry.digest(fingerprints),
    }

    paths, closure_hash = registry._runtime_source_closure(
        tmp_path,
        evidence,
        expected_root_paths=root_paths,
        project_paths=source_paths,
        project={
            "roots": ["q3.lean.aristotle/Q3"],
            "file_count": 2,
        },
    )

    assert paths == source_paths
    assert len(closure_hash) == 64
    assert calls == [("ls-tree", "-rz", "HEAD", "--", *source_paths)]


@pytest.mark.parametrize("plant", ["empty", "subset", "extra", "reordered"])
def test_runtime_source_closure_requires_exact_prebuild_roots(
    tmp_path: Path, monkeypatch, plant: str
) -> None:
    source_paths = [
        "q3.lean.aristotle/Q3/A.lean",
        "q3.lean.aristotle/Q3/B.lean",
    ]
    fingerprints = []
    for index, rel in enumerate(source_paths):
        path = tmp_path / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"theorem t{index} : True := by trivial\n", encoding="utf-8")
        fingerprints.append({"path": rel, "sha256": registry._file_sha256(path)})
    monkeypatch.setattr(
        registry,
        "_git_bytes",
        lambda repo, *args: b"".join(
            f"100644 blob {'a' * 39}{index}\t{rel}\0".encode()
            for index, rel in enumerate(source_paths)
        ),
    )
    monkeypatch.setattr(registry, "_path_has_symlink", lambda repo, path: False)
    roots = source_paths.copy()
    prebuild = copy.deepcopy(fingerprints)
    if plant == "empty":
        prebuild = []
    elif plant == "subset":
        prebuild = prebuild[:1]
    elif plant == "extra":
        prebuild.append({"path": source_paths[0], "sha256": "c" * 64})
    else:
        prebuild.reverse()
    evidence = {
        "source_paths": source_paths,
        "source_fingerprints": fingerprints,
        "root_source_paths": roots,
        "prebuild_root_source_fingerprints": prebuild,
        "project_source_baseline": {
            "root_path": "q3.lean.aristotle/Q3",
            "file_count": 2,
            "algorithm": "PATH_TAB_CONTENT_SHA256_NEWLINE_V1",
            "tree_sha256": "b" * 64,
        },
        "source_map_sha256": registry.digest(fingerprints),
    }
    with pytest.raises(
        registry.NodeRegistryError, match="PREBUILD_SOURCE_EVIDENCE_INVALID"
    ):
        registry._runtime_source_closure(
            tmp_path,
            evidence,
            expected_root_paths=roots,
            project_paths=source_paths,
            project={"roots": ["q3.lean.aristotle/Q3"], "file_count": 2},
        )


def test_writer_read_lock_fails_closed_on_collision(tmp_path: Path, monkeypatch) -> None:
    lock_path = tmp_path / "writer.lock"
    lock_path.write_bytes(b"")
    monkeypatch.setattr(registry, "_git", lambda repo, *args: str(lock_path))
    with registry._writer_read_lock(ROOT):
        pass
    with lock_path.open("rb") as held:
        fcntl.flock(held.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(registry.NodeRegistryError, match="WRITER_LOCK_COLLISION"):
            with registry._writer_read_lock(ROOT):
                pass


def test_writer_read_lock_detects_transient_inode_swap(tmp_path: Path, monkeypatch) -> None:
    lock_path = tmp_path / "writer.lock"
    parked_path = tmp_path / "writer.lock.parked"
    lock_path.write_bytes(b"")
    monkeypatch.setattr(registry, "_git", lambda repo, *args: str(lock_path))

    with pytest.raises(registry.NodeRegistryError, match="WRITER_LOCK_IDENTITY_CHANGED"):
        with registry._writer_read_lock(ROOT):
            lock_path.rename(parked_path)
            lock_path.write_bytes(b"replacement")
            lock_path.unlink()
            parked_path.rename(lock_path)


def test_startup_fast_path_scopes_physical_goal_and_never_runs_lean(monkeypatch) -> None:
    monkeypatch.setattr(
        lean_dependency_runtime,
        "inspect_dependencies",
        lambda *args, **kwargs: (_ for _ in ()).throw(AssertionError("deep probe at startup")),
    )
    monkeypatch.setattr(
        registry,
        "_validate_historical_receipts",
        lambda *args, **kwargs: (_ for _ in ()).throw(AssertionError("v9 history at startup")),
    )
    document = live()
    monkeypatch.setattr(registry, "_dirty_paths", lambda repo, paths: set())
    monkeypatch.setattr(registry, "load_registry", lambda repo: document)
    summary = registry.startup_gate_summary(ROOT, GOAL)
    assert summary == {
        "schema": registry.SUMMARY_SCHEMA,
        "status": "HOLD",
        "code": "NODE_REGISTRY_EXACT_EDGE_REQUIRED",
        "registry_hash": document["registry_hash"],
        "node_count": 7,
        "edge_count": 9,
        "historical_v9_unmapped": 3,
        "consumption_status": "NOT_RUN_STARTUP_FAST_PATH",
    }
    assert registry.startup_gate_summary(ROOT, "docs/routeB_bus/999.goal.md")["code"] == (
        "NODE_REGISTRY_SELECTED_SCOPE_UNREGISTERED"
    )


def test_startup_summary_is_zero_git_structural_scope_only(monkeypatch) -> None:
    monkeypatch.setattr(
        registry,
        "_git",
        lambda *args, **kwargs: (_ for _ in ()).throw(AssertionError("git at startup")),
    )
    monkeypatch.setattr(
        registry,
        "_git_bytes",
        lambda *args, **kwargs: (_ for _ in ()).throw(AssertionError("git at startup")),
    )
    summary = registry.startup_gate_summary(ROOT, GOAL)
    assert summary["status"] == "HOLD"
    assert summary["code"] == "NODE_REGISTRY_EXACT_EDGE_REQUIRED"


def test_exact_unmapped_historical_node_is_never_startup_pass() -> None:
    node = next(
        row for row in live()["nodes"] if row["lifecycle"] == "HISTORICAL_V9_UNMAPPED"
    )
    summary = registry.startup_gate_summary(ROOT, node["node_id"])
    assert summary["status"] == "HOLD"
    assert summary["code"] == "NODE_REGISTRY_HISTORICAL_V9_UNMAPPED"


def test_startup_exact_pin_triple_selects_one_edge_and_fails_closed() -> None:
    document = live()
    node = document["nodes"][0]
    edge = document["edges"][0]
    summary = registry.startup_gate_summary(
        ROOT,
        GOAL,
        exact_node_pin=node["node_id"],
        exact_theorem_pin=edge["theorem"],
        exact_consumer_pin=edge["consumer"],
    )
    assert summary["status"] == "PASS"
    assert summary["node_count"] == 1
    assert summary["historical_v9_unmapped"] == 0
    task_summary = registry.startup_gate_summary(
        ROOT,
        node["validation_inputs"]["task_path"],
        exact_node_pin=node["node_id"],
        exact_theorem_pin=edge["theorem"],
        exact_consumer_pin=edge["consumer"],
    )
    assert task_summary["status"] == "PASS"

    incomplete = registry.startup_gate_summary(
        ROOT, GOAL, exact_node_pin=node["node_id"]
    )
    assert incomplete["status"] == "FATAL"
    assert "EXACT_EDGE_PIN_INCOMPLETE" in incomplete["detail"]
    mismatch = registry.startup_gate_summary(
        ROOT,
        GOAL,
        exact_node_pin=node["node_id"],
        exact_theorem_pin=edge["theorem"] + "Missing",
        exact_consumer_pin=edge["consumer"],
    )
    assert mismatch["status"] == "FATAL"
    assert "EXACT_EDGE_PIN_INVALID" in mismatch["detail"]
    drift = registry.startup_gate_summary(
        ROOT,
        "docs/Codex/TASK_wrong.md",
        exact_node_pin=node["node_id"],
        exact_theorem_pin=edge["theorem"],
        exact_consumer_pin=edge["consumer"],
    )
    assert drift["status"] == "FATAL"
    assert "EXACT_EDGE_PIN_GOAL_DRIFT" in drift["detail"]


def test_helper_auto_only_without_semantic_triggers_and_ambiguity_is_bridge() -> None:
    empty = {field: [] for field in registry.SEMANTIC_TRIGGER_FIELDS}
    assert registry.classify_node(empty) == "HELPER"
    with_edge = dict(empty, exact_edges=["E"])
    assert registry.classify_node(with_edge) == "SEMANTIC_BRIDGE"
    ambiguous = dict(empty, object="AMBIGUOUS")
    assert registry.classify_node(ambiguous) == "SEMANTIC_BRIDGE"
    assert registry.classify_node(empty, roof_change=True) == "ROOF_CHANGE"


def test_semantic_hash_excludes_blobs_but_binds_hypothesis_port() -> None:
    document = live()
    node = document["nodes"][0]
    edge_map = {edge["edge_id"]: edge for edge in document["edges"]}
    original = registry._semantic_review_digest(node["semantic_review_inputs"], edge_map)
    changed_body = copy.deepcopy(node["semantic_review_inputs"])
    changed_body["proof_body"] = "different tactic"
    changed_body.pop("proof_body")
    assert registry._semantic_review_digest(changed_body, edge_map) == original
    blob_changed = copy.deepcopy(edge_map)
    blob_changed["E001"]["consumer_blob"] = "0" * 40
    assert registry._semantic_review_digest(node["semantic_review_inputs"], blob_changed) == (
        original
    )
    assert registry._validation_digest(
        node["validation_inputs"], node["semantic_review_inputs"]["exact_edges"], blob_changed
    ) != registry._validation_digest(
        node["validation_inputs"], node["semantic_review_inputs"]["exact_edges"], edge_map
    )
    changed_edges = copy.deepcopy(edge_map)
    changed_edges["E001"]["hypothesis_port"]["surface"] = "ELABORATED_TYPE"
    assert (
        registry._semantic_review_digest(node["semantic_review_inputs"], changed_edges) != original
    )
    assert set(node["validation_inputs"]) >= {
        "source_bytes",
        "toolchain",
        "build",
        "holes",
        "axioms",
        "dependency_graph",
    }


def test_self_review_never_opens_and_roof_needs_owner_plus_second() -> None:
    document = live()
    node = document["nodes"][0]
    node["review"]["reviewers"] = ["SELF_REVIEW"]
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="SELF_REVIEW"):
        registry._validate_registry(document)

    document = live()
    node = document["nodes"][0]
    node["node_class"] = "ROOF_CHANGE"
    node["source"]["path"] = registry.ROOF_SOURCE
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="REVIEW_INSUFFICIENT"):
        registry._validate_registry(document)


def test_roof_source_identity_cannot_be_laundered_as_semantic_bridge() -> None:
    document = live()
    node = document["nodes"][0]
    node["source"]["path"] = registry.ROOF_SOURCE
    node["node_class"] = "SEMANTIC_BRIDGE"
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="CLASSIFICATION_DRIFT"):
        registry._validate_registry(document)


def test_lifecycle_review_coupling_and_native_receipt_independence() -> None:
    document = live()
    node = document["nodes"][2]
    node["lifecycle"] = "ADMITTED"
    node["validation_inputs"]["dependency_graph"].pop(
        "historical_entry_binding_sha256"
    )
    node["semantic_review_inputs"]["definitions"] = [
        {
            "name": definition["name"],
            "type_fingerprint": expr_fingerprint(index + 20),
            "value_fingerprint": expr_fingerprint(index + 30),
        }
        for index, definition in enumerate(node["semantic_review_inputs"]["definitions"])
    ]
    node["semantic_review_inputs"]["elaborated_types"] = [
        {"theorem": theorem, "type_fingerprint": expr_fingerprint(index + 40)}
        for index, theorem in enumerate(node["theorem_ids"])
    ]
    node["review"].update(
        state="NOT_OPENED",
        reviewers=[],
        evidence=[],
        historical_receipt=None,
    )
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="ADMITTED_REVIEW_NOT_OPENED"):
        registry._validate_registry(document)

    node["lifecycle"] = "CANDIDATE"
    rehash(document)
    registry._validate_registry(document)
    registry._validate_historical_receipts(ROOT, document, [node])


def test_external_and_adversarial_review_evidence_fail_closed() -> None:
    document = live()
    node = document["nodes"][1]
    evidence = node["review"]["evidence"][0]
    node["review"]["reviewers"] = ["EXTERNAL_SIGNED"]
    evidence.update(
        reviewer_class="EXTERNAL_SIGNED",
        signed=False,
        principal="external-reviewer",
        key_id=None,
        signature=None,
    )
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="EXTERNAL_REVIEW_UNSIGNED"):
        registry._validate_registry(document)

    evidence.update(signed=True, key_id="untrusted-key", signature="not-verified")
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="EXTERNAL_REVIEW_VERIFIER_UNAVAILABLE"):
        registry._validate_registry(document)

    document = live()
    node = document["nodes"][1]
    evidence = node["review"]["evidence"][0]
    node["review"]["reviewers"] = ["ADVERSARIAL_READ_ONLY"]
    evidence.update(
        reviewer_class="ADVERSARIAL_READ_ONLY",
        signed=False,
        converged=False,
        read_only=False,
        principal="local-adversarial-reviewer",
        key_id=None,
        signature=None,
    )
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="ADVERSARIAL_REVIEW_NOT_CONVERGED"):
        registry._validate_registry(document)


def test_roof_review_accepts_owner_only_with_second_valid_reviewer() -> None:
    document = live()
    node = document["nodes"][1]
    node["node_class"] = "ROOF_CHANGE"
    node["source"]["path"] = registry.ROOF_SOURCE
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="REVIEW_INSUFFICIENT"):
        registry._validate_registry(document)

    owner_evidence = node["review"]["evidence"][0]
    second = copy.deepcopy(owner_evidence)
    second.update(
        reviewer_class="ADVERSARIAL_READ_ONLY",
        reviewer_id="LOCAL_ADVERSARIAL_READ_ONLY_REVIEW",
        signed=False,
        converged=True,
        read_only=True,
        principal="local-adversarial-reviewer",
        key_id=None,
        signature=None,
    )
    node["review"]["reviewers"] = ["OWNER_SIGNOFF", "ADVERSARIAL_READ_ONLY"]
    node["review"]["evidence"].append(second)
    rehash(document)
    registry._validate_registry(document)


def test_px_rh_claim_cannot_be_set() -> None:
    document = live()
    document["nodes"][0]["px_rh_claim"] = True
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="PX_RH_CLAIM"):
        registry._validate_registry(document)


def deep_fixture(monkeypatch) -> tuple[dict, dict, dict]:
    document = live()
    node = copy.deepcopy(document["nodes"][0])
    edge = copy.deepcopy(document["edges"][0])
    document["nodes"] = [node]
    document["edges"] = [edge]
    node["lifecycle"] = "ADMITTED"
    node["review"] = {
        "state": "CLOSED",
        "reviewers": ["OWNER_SIGNOFF"],
        "historical_receipt": None,
        "transport": "OFFLINE_EMBEDDED_NO_SOCKET",
        "evidence": [
            {
                "reviewer_class": "OWNER_SIGNOFF",
                "reviewer_id": "OWNER_PHASE_A_TEST",
                "verdict": "APPROVE",
                "exact_payload_hash": "0" * 64,
                "signed": False,
                "converged": True,
                "read_only": True,
                "principal": "OWNER",
                "key_id": None,
                "signature": None,
            }
        ],
    }
    project_path = node["source"]["path"]
    consumer_path = edge["consumer_path"]
    consumer_sha256 = "d" * 64
    tree_hash = "1" * 64
    document["project"] = {
        "roots": ["q3.lean.aristotle/Q3"],
        "root_count": 1,
        "file_count": 2,
        "project_dependency_tree_hash": tree_hash,
    }
    theorem_types = {
        theorem: expr_fingerprint(index + 100)
        for index, theorem in enumerate(node["theorem_ids"])
    }
    definition_name = "Q3.Plant.VerifiedDefinition"
    definition_type = expr_fingerprint(900)
    definition_value = expr_fingerprint(901)
    node["semantic_review_inputs"]["definitions"] = [
        {
            "name": definition_name,
            "type_fingerprint": definition_type,
            "value_fingerprint": definition_value,
        }
    ]
    node["semantic_review_inputs"]["elaborated_types"] = [
        {"theorem": theorem, "type_fingerprint": value}
        for theorem, value in theorem_types.items()
    ]
    consumptions = [
        {
            "theorem": edge["theorem"],
            "consumer": edge["consumer"],
            "relation": edge["relation"],
            "path": edge["path"],
            "hypothesis_port": edge["hypothesis_port"],
        }
    ]
    node["validation_inputs"]["axioms"]["sha256"] = registry.digest(
        {theorem: ["Classical.choice"] for theorem in node["theorem_ids"]}
    )
    node["validation_inputs"]["dependency_graph"].update(
        project_dependency_tree_hash=tree_hash,
        sha256=registry.digest(consumptions),
    )
    node["validation_inputs"]["dependency_graph"].pop(
        "historical_entry_binding_sha256", None
    )
    rehash(document)
    module = registry._module_from_path(project_path)
    consumer_module = registry._module_from_path(consumer_path)
    import_modules = sorted({module, consumer_module})
    root_fingerprints = [
        {
            "path": path,
            "sha256": (
                node["validation_inputs"]["source_bytes"]["sha256"]
                if path == project_path
                else consumer_sha256
            ),
        }
        for path in sorted({project_path, consumer_path})
    ]
    snapshot = {
        "schema": lean_dependency_runtime.SCHEMA,
        "algorithm_version": lean_dependency_runtime.ALGORITHM_VERSION,
        "import_modules": import_modules,
        "target_declarations": sorted(node["theorem_ids"]),
        "semantic_declarations": [definition_name],
        "project_dependency_tree_hash": tree_hash,
        "declarations": [
            {
                "name": theorem,
                "module": module,
                "direct_refs": [],
                "type_fingerprint": theorem_types[theorem],
                "value_fingerprint": None,
                "axioms": ["Classical.choice"],
            }
            for theorem in node["theorem_ids"]
        ]
        + [
            {
                "name": edge["consumer"],
                "module": consumer_module,
                "direct_refs": [edge["theorem"]],
                "type_fingerprint": expr_fingerprint(800),
                "value_fingerprint": None,
                "axioms": ["Classical.choice"],
            },
            {
                "name": definition_name,
                "module": module,
                "direct_refs": [],
                "type_fingerprint": definition_type,
                "value_fingerprint": definition_value,
                "axioms": ["Classical.choice"],
            }
        ],
        "consumptions": copy.deepcopy(consumptions),
        "runtime_evidence": {
            "build_run": {
                "command": ["lake", "build", *import_modules],
                "returncode": 0,
            },
            "graph_run": {"command": ["lake", "env", "lean", "--stdin"], "returncode": 0},
            "metadata_run": {"command": ["lake", "env", "lean", "--stdin"], "returncode": 0},
            "source_paths": [row["path"] for row in root_fingerprints],
            "source_fingerprints": root_fingerprints,
            "root_source_paths": [row["path"] for row in root_fingerprints],
            "prebuild_root_source_fingerprints": root_fingerprints,
            "project_source_baseline": {
                "root_path": "q3.lean.aristotle/Q3",
                "file_count": 2,
                "algorithm": "PATH_TAB_CONTENT_SHA256_NEWLINE_V1",
                "tree_sha256": "e" * 64,
            },
            "source_map_sha256": registry.digest(root_fingerprints),
            "holes": [],
        },
    }
    monkeypatch.setattr(
        registry,
        "_project_tree_at_head",
        lambda repo, roots: (sorted({project_path, consumer_path}), 2, tree_hash),
    )
    monkeypatch.setattr(registry, "_dirty_paths", lambda repo, paths: set())
    monkeypatch.setattr(registry, "_path_has_symlink", lambda repo, path: False)
    monkeypatch.setattr(registry, "_is_ancestor", lambda repo, commit: True)
    monkeypatch.setattr(
        registry, "_blob_at_commit", lambda repo, commit, path: node["source"]["blob"]
    )
    monkeypatch.setattr(
        registry,
        "_blobs_at_head",
        lambda repo, paths: {
            path: edge["consumer_blob"]
            if path == edge["consumer_path"]
            else node["source"]["blob"]
            for path in paths
        },
    )
    file_hashes = {
        project_path: node["validation_inputs"]["source_bytes"]["sha256"],
        consumer_path: consumer_sha256,
        node["validation_inputs"]["toolchain"]["path"]: node["validation_inputs"]["toolchain"][
            "sha256"
        ],
        "q3.lean.aristotle/lakefile.toml": node["validation_inputs"]["build"]["lakefile_sha256"],
        "q3.lean.aristotle/lake-manifest.json": node["validation_inputs"]["build"][
            "manifest_sha256"
        ],
    }
    monkeypatch.setattr(
        registry, "_file_sha256", lambda path: file_hashes[str(path.relative_to(ROOT))]
    )
    monkeypatch.setattr(registry, "_git", lambda repo, *args: "a" * 40)
    monkeypatch.setattr(
        registry, "_validate_historical_receipts", lambda repo, value, scoped=None: None
    )
    return document, snapshot, node


def test_verify_consumption_exact_direct_pass(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    edge = document["edges"][0]
    result = registry._verify_consumption(
        ROOT,
        document,
        selected_goal_path=node["validation_inputs"]["task_path"],
        dependency_snapshot=snapshot,
        exact_node_pin=node["node_id"],
        exact_theorem_pin=edge["theorem"],
        exact_consumer_pin=edge["consumer"],
    )
    assert result["status"] == "PASS"
    assert result["edge_count"] == 1
    assert_complete_validation_evidence(result)
    with pytest.raises(registry.NodeRegistryError, match="EXACT_EDGE_PIN_INCOMPLETE"):
        registry._verify_consumption(
            ROOT,
            document,
            selected_goal_path=node["validation_inputs"]["task_path"],
            dependency_snapshot=snapshot,
            exact_node_pin=node["node_id"],
        )
    with pytest.raises(registry.NodeRegistryError, match="EXACT_EDGE_PIN_INVALID"):
        registry._verify_consumption(
            ROOT,
            document,
            selected_goal_path=node["validation_inputs"]["task_path"],
            dependency_snapshot=snapshot,
            exact_node_pin=node["node_id"],
            exact_theorem_pin=edge["theorem"] + "B",
            exact_consumer_pin=edge["consumer"],
        )


def test_exact_pair_pin_preserves_all_distinct_first_hop_ports(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    first = document["edges"][0]
    second = copy.deepcopy(first)
    second.update(
        edge_id="E999",
        relation="TRANSITIVE",
        path=[first["consumer"], "Q3.Plant.SecondPort", first["theorem"]],
        hypothesis_port={
            "surface": "ELABORATED_VALUE",
            "direct_reference": "Q3.Plant.SecondPort",
        },
    )
    document["edges"].append(second)
    node["semantic_review_inputs"]["exact_edges"].append(second["edge_id"])
    second_port_type = expr_fingerprint(910)
    second_port_value = expr_fingerprint(911)
    node["semantic_review_inputs"]["definitions"].append(
        {
            "name": "Q3.Plant.SecondPort",
            "type_fingerprint": second_port_type,
            "value_fingerprint": second_port_value,
        }
    )
    snapshot["semantic_declarations"].append("Q3.Plant.SecondPort")
    snapshot["semantic_declarations"].sort()
    snapshot["declarations"].append(
        {
            "name": "Q3.Plant.SecondPort",
            "module": snapshot["import_modules"][0],
            "direct_refs": [],
            "type_fingerprint": second_port_type,
            "value_fingerprint": second_port_value,
            "axioms": ["Classical.choice"],
        }
    )
    second_consumption = registry._dependency_edge_payload(second)
    snapshot["consumptions"].append(second_consumption)
    ordered_consumptions = sorted(
        snapshot["consumptions"],
        key=lambda row: (
            row["theorem"],
            row["consumer"],
            row["hypothesis_port"]["surface"],
            row["hypothesis_port"]["direct_reference"],
        ),
    )
    node["validation_inputs"]["dependency_graph"]["sha256"] = registry.digest(
        ordered_consumptions
    )
    rehash(document)
    registry._validate_registry(document)

    result = registry._verify_consumption(
        ROOT,
        document,
        selected_goal_path=node["validation_inputs"]["task_path"],
        dependency_snapshot=snapshot,
        exact_node_pin=node["node_id"],
        exact_theorem_pin=first["theorem"],
        exact_consumer_pin=first["consumer"],
    )
    assert result["status"] == "PASS"
    assert result["edge_count"] == 2
    assert len(result["validation_evidence"][0]["dependency_result"]["edges"]) == 2

    snapshot["consumptions"].reverse()
    reordered = registry._verify_consumption(
        ROOT,
        document,
        selected_goal_path=node["validation_inputs"]["task_path"],
        dependency_snapshot=snapshot,
        exact_node_pin=node["node_id"],
        exact_theorem_pin=first["theorem"],
        exact_consumer_pin=first["consumer"],
    )
    assert reordered["status"] == "PASS"
    assert reordered["validation_evidence"][0]["dependency_result"] == (
        result["validation_evidence"][0]["dependency_result"]
    )

    unknown = copy.deepcopy(second_consumption)
    unknown["path"][1] = "Q3.Plant.UnknownPort"
    unknown["hypothesis_port"]["direct_reference"] = "Q3.Plant.UnknownPort"
    snapshot["consumptions"].append(unknown)
    with pytest.raises(registry.NodeRegistryError, match="HYPOTHESIS_PORT_DRIFT"):
        registry._verify_consumption(
            ROOT,
            document,
            selected_goal_path=node["validation_inputs"]["task_path"],
            dependency_snapshot=snapshot,
            exact_node_pin=node["node_id"],
            exact_theorem_pin=first["theorem"],
            exact_consumer_pin=first["consumer"],
        )


def test_clean_candidate_runs_full_validation_but_is_never_consumable(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    node["lifecycle"] = "CANDIDATE"
    rehash(document)
    result = registry._verify_consumption(
        ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
    )
    assert result["status"] == "CANDIDATE_VALIDATED_NOT_CONSUMABLE"
    assert result["dirty_owned_paths"] == []
    assert result["validation_evidence"][0]["dependency_result"]["status"] == "EXACT"
    assert_complete_validation_evidence(result)

    snapshot["runtime_evidence"]["holes"] = [{"path": node["source"]["path"], "line": 1}]
    with pytest.raises(registry.NodeRegistryError, match="RELEVANT_CLOSURE_HOLE_PRESENT"):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )


def test_verify_catches_wrapper_laundering_and_unregistered_theorem_b(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    theorem = node["theorem_ids"][0]
    next(row for row in snapshot["declarations"] if row["name"] == theorem)[
        "type_fingerprint"
    ] = expr_fingerprint(777)
    snapshot["consumptions"][0].update(
        relation="TRANSITIVE",
        path=[
            snapshot["consumptions"][0]["consumer"],
            "Q3.Plant.Wrapper",
            snapshot["consumptions"][0]["theorem"],
        ],
    )
    with pytest.raises(registry.NodeRegistryError, match="WRAPPER_LAUNDERING"):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )

    document, snapshot, node = deep_fixture(monkeypatch)
    snapshot["consumptions"][0]["hypothesis_port"]["surface"] = "ELABORATED_TYPE"
    with pytest.raises(registry.NodeRegistryError, match="HYPOTHESIS_PORT_DRIFT"):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )

    document, snapshot, node = deep_fixture(monkeypatch)
    theorem_b = node["theorem_ids"][1]
    snapshot["consumptions"].append(
        {
            "theorem": theorem_b,
            "consumer": "Q3.Plant.Unregistered",
            "relation": "DIRECT",
            "path": ["Q3.Plant.Unregistered", theorem_b],
            "hypothesis_port": {
                "surface": "ELABORATED_VALUE",
                "direct_reference": theorem_b,
            },
        }
    )
    with pytest.raises(registry.NodeRegistryError, match="UNREGISTERED_CONSUMPTION"):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )


def test_owned_dirty_compiles_exact_bytes_but_remains_unconsumable(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    source = node["source"]["path"]
    source_sha256 = node["validation_inputs"]["source_bytes"]["sha256"]
    monkeypatch.setattr(registry, "_dirty_paths", lambda repo, paths: {source})
    monkeypatch.setattr(
        lean_dependency_runtime,
        "validate_candidate_sources",
        lambda repo, paths: [candidate_receipt(source, source_sha256)],
    )
    result = registry._verify_consumption(
        ROOT,
        document,
        selected_goal_path=node["node_id"],
        owned_paths=[source],
        dependency_snapshot=snapshot,
    )
    assert result["status"] == "CANDIDATE_VALIDATED_NOT_CONSUMABLE"
    assert result["candidate_compile_receipts"][0]["bytes_sha256"] == source_sha256


@pytest.mark.parametrize(
    "plant",
    ["missing_field", "wrong_path", "nonzero", "wrong_bytes", "candidate_set"],
)
def test_owned_dirty_candidate_receipt_is_exact(monkeypatch, plant: str) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    source = node["source"]["path"]
    source_sha256 = node["validation_inputs"]["source_bytes"]["sha256"]
    receipt = candidate_receipt(source, source_sha256)
    if plant == "missing_field":
        receipt.pop("stderr_sha256")
    elif plant == "wrong_path":
        receipt["path"] = "q3.lean.aristotle/Q3/Plant/Wrong.lean"
    elif plant == "nonzero":
        receipt["returncode"] = 1
    elif plant == "wrong_bytes":
        receipt["bytes_sha256"] = "c" * 64
    else:
        receipt["candidate_set"] = []
    monkeypatch.setattr(registry, "_dirty_paths", lambda repo, paths: {source})
    monkeypatch.setattr(
        lean_dependency_runtime,
        "validate_candidate_sources",
        lambda repo, paths: [receipt],
    )
    error = (
        "CANDIDATE_BYTES_MUTATION_DURING_PROBE"
        if plant == "wrong_bytes"
        else "CANDIDATE_RECEIPT_INVALID"
    )
    with pytest.raises(registry.NodeRegistryError, match=error):
        registry._verify_consumption(
            ROOT,
            document,
            selected_goal_path=node["node_id"],
            owned_paths=[source],
            dependency_snapshot=snapshot,
        )


@pytest.mark.parametrize(
    ("plant", "message"),
    [
        ("foreign_dirty", "FOREIGN_RELEVANT_DIRTY"),
        ("symlink", "SYMLINK_MUTATION"),
        ("head", "HEAD_MUTATION"),
    ],
)
def test_mutation_plants_fail_closed(monkeypatch, plant: str, message: str) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    source = node["source"]["path"]
    if plant == "foreign_dirty":
        monkeypatch.setattr(registry, "_dirty_paths", lambda repo, paths: {source})
    elif plant == "symlink":
        monkeypatch.setattr(registry, "_path_has_symlink", lambda repo, path: path == source)
    elif plant == "head":
        heads = iter(["a" * 40, "b" * 40])
        monkeypatch.setattr(registry, "_git", lambda repo, *args: next(heads))
    with pytest.raises(registry.NodeRegistryError, match=message):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )


def test_clean_committed_source_blob_drift_requires_validation_not_semantic_review(
    monkeypatch,
) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    changed_blob = "0" * 40
    monkeypatch.setattr(
        registry,
        "_blobs_at_head",
        lambda repo, paths: {path: changed_blob for path in paths},
    )
    semantic_hash = node["semantic_review_hash"]
    result = registry._verify_consumption(
        ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
    )
    assert result["status"] == "VALIDATION_REQUIRED"
    assert result["semantic_review_hash_unchanged"] is True
    assert node["semantic_review_hash"] == semantic_hash
    assert result["validation_evidence"][0]["source_blob"] == changed_blob
    assert_complete_validation_evidence(result)


def test_physical_goal_requires_one_exact_node_edge_or_consumer(monkeypatch) -> None:
    monkeypatch.setattr(
        lean_dependency_runtime,
        "inspect_dependencies",
        lambda *args, **kwargs: (_ for _ in ()).throw(AssertionError("ambiguous scope probed")),
    )
    monkeypatch.setattr(registry, "_validate_historical_receipts", lambda repo, value: None)
    result = registry._verify_consumption(ROOT, live(), selected_goal_path=GOAL)
    assert result["status"] == "EXACT_EDGE_REQUIRED"
    assert result["code"] == "NODE_REGISTRY_EXACT_EDGE_REQUIRED"
    assert len(result["candidate_node_ids"]) == 7
    assert len(result["candidate_edge_ids"]) == 9


def test_exact_consumer_scopes_only_its_registered_edge(monkeypatch) -> None:
    document, snapshot, _node = deep_fixture(monkeypatch)
    edge = document["edges"][0]
    result = registry._verify_consumption(
        ROOT,
        document,
        selected_goal_path=edge["consumer"],
        dependency_snapshot=snapshot,
    )
    assert result["status"] == "PASS"
    assert result["edge_count"] == 1


@pytest.mark.parametrize("surface", ["theorem", "consumer"])
def test_declaration_modules_bind_source_and_consumer_paths(
    monkeypatch, surface: str
) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    edge = document["edges"][0]
    declaration_name = node["theorem_ids"][0] if surface == "theorem" else edge["consumer"]
    declaration = next(
        row for row in snapshot["declarations"] if row["name"] == declaration_name
    )
    declaration["module"] = "Q3.Plant.WrongModule"

    with pytest.raises(
        registry.NodeRegistryError, match="DECLARATION_MODULE_BINDING_DRIFT"
    ):
        registry._verify_consumption(
            ROOT,
            document,
            selected_goal_path=node["node_id"],
            dependency_snapshot=snapshot,
        )


def test_deep_probe_imports_only_scoped_source_and_consumer(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    edge = document["edges"][0]
    unrelated = "q3.lean.aristotle/Q3/Unrelated.lean"
    project_paths = sorted(
        {node["source"]["path"], edge["consumer_path"], unrelated}
    )
    document["project"]["file_count"] = len(project_paths)
    snapshot["runtime_evidence"]["project_source_baseline"]["file_count"] = len(
        project_paths
    )
    rehash(document)
    monkeypatch.setattr(
        registry,
        "_project_tree_at_head",
        lambda repo, roots: (
            project_paths,
            len(project_paths),
            document["project"]["project_dependency_tree_hash"],
        ),
    )
    calls: list[list[str]] = []

    def inspect(repo, *, import_modules, target_declarations, semantic_declarations):
        calls.append(list(import_modules))
        return copy.deepcopy(snapshot)

    monkeypatch.setattr(lean_dependency_runtime, "inspect_dependencies", inspect)
    result = registry._verify_consumption(
        ROOT,
        document,
        selected_goal_path=edge["consumer"],
    )
    expected_modules = sorted(
        {
            registry._module_from_path(node["source"]["path"]),
            registry._module_from_path(edge["consumer_path"]),
        }
    )
    assert result["status"] == "PASS"
    assert calls == [expected_modules]
    assert registry._module_from_path(unrelated) not in calls[0]


def test_public_consumption_rejects_embedded_native_admission_authority(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    edge = document["edges"][0]
    calls: list[tuple[list[str], list[str], list[str]]] = []

    def inspect(repo, *, import_modules, target_declarations, semantic_declarations):
        calls.append(
            (
                list(import_modules),
                list(target_declarations),
                list(semantic_declarations),
            )
        )
        return copy.deepcopy(snapshot)

    monkeypatch.setattr(lean_dependency_runtime, "inspect_dependencies", inspect)
    monkeypatch.setattr(registry, "load_registry", lambda repo: document)
    monkeypatch.setattr(registry, "_writer_read_lock", lambda repo: nullcontext())
    with pytest.raises(
        registry.NodeRegistryError,
        match="EXACT_EDGE_PIN_INCOMPLETE",
    ):
        registry.verify_consumption(
            ROOT,
            selected_goal_path=edge["consumer"],
        )
    assert calls == []
    with pytest.raises(
        registry.NodeRegistryError,
        match="NATIVE_ADMISSION_AUTHORITY_UNAVAILABLE",
    ):
        registry.verify_consumption(
            ROOT,
            selected_goal_path=node["validation_inputs"]["task_path"],
            exact_node_pin=node["node_id"],
            exact_theorem_pin=edge["theorem"],
            exact_consumer_pin=edge["consumer"],
        )
    assert calls == []
    with pytest.raises(TypeError):
        registry.verify_consumption(  # type: ignore[call-arg]
            ROOT,
            document,
            selected_goal_path=node["node_id"],
        )
    with pytest.raises(TypeError):
        registry.verify_consumption(  # type: ignore[call-arg]
            ROOT,
            selected_goal_path=node["node_id"],
            dependency_snapshot=snapshot,
        )


def test_historical_type_placeholder_requires_semantic_review(
    monkeypatch,
) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    historical = live()["nodes"][0]
    node["lifecycle"] = "HISTORICAL_V9"
    node["review"] = copy.deepcopy(historical["review"])
    node["validation_inputs"]["dependency_graph"]["historical_entry_binding_sha256"] = (
        historical["validation_inputs"]["dependency_graph"][
            "historical_entry_binding_sha256"
        ]
    )
    node["semantic_review_inputs"]["elaborated_types"] = [
        {"status": "HISTORICAL_V9_NOT_REPROBED"}
    ]
    rehash(document)
    semantic_hash = node["semantic_review_hash"]
    result = registry._verify_consumption(
        ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
    )
    assert result["status"] == "HOLD"
    assert result["code"] == "NODE_REGISTRY_SEMANTIC_REVIEW_REQUIRED"
    assert result["semantic_review_hash_unchanged"] is False
    assert node["semantic_review_hash"] == semantic_hash
    evidence = result["validation_evidence"][0]
    assert evidence["elaborated_type_fingerprints"]
    assert evidence["semantic_review"]["status"] == "REVIEW_REQUIRED"
    assert evidence["semantic_review"]["changed_fields"] == ["elaborated_types"]
    assert evidence["semantic_review"]["current_hash"] == semantic_hash
    assert evidence["semantic_review"]["candidate_hash"] != semantic_hash


def test_native_theorem_type_drift_requires_semantic_review(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    theorem = node["theorem_ids"][0]
    declaration = next(row for row in snapshot["declarations"] if row["name"] == theorem)
    declaration["type_fingerprint"] = expr_fingerprint(777)
    semantic_hash = node["semantic_review_hash"]
    result = registry._verify_consumption(
        ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
    )
    assert result["status"] == "HOLD"
    assert result["code"] == "NODE_REGISTRY_SEMANTIC_REVIEW_REQUIRED"
    assert result["semantic_review_hash_unchanged"] is False
    evidence = result["validation_evidence"][0]
    assert evidence["semantic_review"]["changed_fields"] == ["elaborated_types"]
    assert evidence["semantic_review"]["current_hash"] == semantic_hash
    assert evidence["semantic_review"]["candidate_hash"] != semantic_hash


def test_empty_historical_definition_surface_is_stable_and_does_not_refresh_loop(
    monkeypatch,
) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    historical = live()["nodes"][0]
    node["lifecycle"] = "HISTORICAL_V9"
    node["review"] = copy.deepcopy(historical["review"])
    node["validation_inputs"]["dependency_graph"]["historical_entry_binding_sha256"] = (
        historical["validation_inputs"]["dependency_graph"][
            "historical_entry_binding_sha256"
        ]
    )
    node["semantic_review_inputs"]["definitions"] = []
    snapshot["semantic_declarations"] = []
    rehash(document)
    result = registry._verify_consumption(
        ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
    )
    assert result["status"] == "PASS"
    evidence = result["validation_evidence"][0]
    assert "definitions_status" not in evidence
    assert "semantic_review" not in evidence


def test_named_historical_definition_placeholder_requires_semantic_review(
    monkeypatch,
) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    historical = live()["nodes"][0]
    node["lifecycle"] = "HISTORICAL_V9"
    node["review"] = copy.deepcopy(historical["review"])
    node["validation_inputs"]["dependency_graph"]["historical_entry_binding_sha256"] = (
        historical["validation_inputs"]["dependency_graph"][
            "historical_entry_binding_sha256"
        ]
    )
    definition_name = node["semantic_review_inputs"]["definitions"][0]["name"]
    node["semantic_review_inputs"]["definitions"] = [
        {"name": definition_name, "status": "HISTORICAL_V9_NOT_REPROBED"}
    ]
    rehash(document)
    semantic_hash = node["semantic_review_hash"]

    result = registry._verify_consumption(
        ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
    )
    assert result["status"] == "HOLD"
    assert result["code"] == "NODE_REGISTRY_SEMANTIC_REVIEW_REQUIRED"
    assert result["semantic_review_hash_unchanged"] is False
    evidence = result["validation_evidence"][0]
    assert evidence["definition_fingerprints"]
    assert evidence["semantic_review"]["status"] == "REVIEW_REQUIRED"
    assert evidence["semantic_review"]["changed_fields"] == ["definitions"]
    assert evidence["semantic_review"]["current_hash"] == semantic_hash
    assert evidence["semantic_review"]["candidate_hash"] != semantic_hash


def test_native_definition_missing_and_fake_fail_closed(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    node["semantic_review_inputs"]["definitions"] = []
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="DEFINITIONS_MISSING"):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )

    document, snapshot, node = deep_fixture(monkeypatch)
    node["semantic_review_inputs"]["definitions"][0]["name"] = "Q3.Plant.Missing"
    snapshot["semantic_declarations"] = ["Q3.Plant.Missing"]
    rehash(document)
    with pytest.raises(registry.NodeRegistryError, match="DEFINITION_MISSING"):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )



@pytest.mark.parametrize("field", ["type_fingerprint", "value_fingerprint"])
def test_native_definition_fingerprint_drift_requires_semantic_review(
    monkeypatch, field: str
) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    definition_name = node["semantic_review_inputs"]["definitions"][0]["name"]
    declaration = next(
        row for row in snapshot["declarations"] if row["name"] == definition_name
    )
    declaration[field] = expr_fingerprint(999)
    semantic_hash = node["semantic_review_hash"]
    result = registry._verify_consumption(
        ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
    )
    assert result["status"] == "HOLD"
    assert result["code"] == "NODE_REGISTRY_SEMANTIC_REVIEW_REQUIRED"
    assert result["semantic_review_hash_unchanged"] is False
    evidence = result["validation_evidence"][0]
    assert evidence["semantic_review"]["changed_fields"] == ["definitions"]
    assert evidence["semantic_review"]["current_hash"] == semantic_hash
    assert evidence["semantic_review"]["candidate_hash"] != semantic_hash


def test_hole_and_axiom_policy_cover_full_relevant_closure(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    snapshot["runtime_evidence"]["holes"] = [
        {"path": "q3.lean.aristotle/Q3/ImportedWrapper.lean", "line": 7}
    ]
    with pytest.raises(registry.NodeRegistryError, match="RELEVANT_CLOSURE_HOLE_PRESENT"):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )

    document, snapshot, node = deep_fixture(monkeypatch)
    snapshot["declarations"].append(
        {
            "name": "Q3.Plant.Consumer",
            "module": "Q3.Plant",
            "direct_refs": [],
            "elaborated_type": "True",
            "elaborated_value": "proof",
            "axioms": ["sorryAx"],
        }
    )
    with pytest.raises(registry.NodeRegistryError, match="AXIOM_POLICY_VIOLATION"):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )


def test_post_probe_project_tree_recheck_fails_closed(monkeypatch) -> None:
    document, snapshot, node = deep_fixture(monkeypatch)
    project_paths = snapshot["runtime_evidence"]["source_paths"]
    rows = iter(
        [
            (project_paths, len(project_paths), "1" * 64),
            (project_paths, len(project_paths), "2" * 64),
        ]
    )
    monkeypatch.setattr(registry, "_project_tree_at_head", lambda repo, roots: next(rows))
    with pytest.raises(registry.NodeRegistryError, match="PROJECT_TREE_MUTATION_DURING_PROBE"):
        registry._verify_consumption(
            ROOT, document, selected_goal_path=node["node_id"], dependency_snapshot=snapshot
        )


def test_historical_receipt_cross_fields_are_locally_bound(monkeypatch) -> None:
    document = live()
    quarantine_bytes = (ROOT / "orchestrator/state/SEMANTIC_QUARANTINE.json").read_bytes()
    monkeypatch.setattr(registry, "_git_bytes", lambda repo, *args: quarantine_bytes)
    document["nodes"][0]["source"]["commit"] = "0" * 40
    with pytest.raises(registry.NodeRegistryError, match="CROSS_FIELD_DRIFT"):
        registry._validate_historical_receipts(ROOT, document)
