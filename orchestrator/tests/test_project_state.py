from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path

import jsonschema
import pytest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("project_state", ROOT / "orchestrator/project_state.py")
assert SPEC and SPEC.loader
ps = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ps)


def load(path: str) -> dict:
    return json.loads((ROOT / path).read_text(encoding="utf-8"))


def test_live_sources_validate_and_views_are_current() -> None:
    ps.validate_sources(ROOT)
    ps.check_views(ROOT)


def test_p5_000_crosswalk_covers_every_board_item() -> None:
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    labels = {registry["p5_000_crosswalk"]["meta"]["migration_label"]} | {
        row["migration_label"] for row in registry["p5_000_crosswalk"]["rows"]
    }
    assert labels == {
        "P5.000_FULL_LABEL_CROSSWALK",
        "P5.001_STATUS_SURFACE_INVENTORY",
        "P5.002_AUTHORITATIVE_STATE_MANIFEST",
        "P5.003_FACT_EXECUTION_SPLIT",
        "P5.004_HASHED_GENERATED_VIEWS",
        "P5.005_NON_SELECTOR_METADATA",
        "P5.006_VIEW_DRIFT_CHECKER",
        "P5.007_APPEND_ONLY_EVENTS",
        "P5.008_BOUNDED_ACTIVE_VIEWS",
    }
    assert registry["owner_label_crosswalk"] == ps.CANONICAL_OWNER_LABEL_CROSSWALK
    assert registry["p5_000_crosswalk"] == ps.CANONICAL_P5_CROSSWALK
    assert registry["event_authority_policy"] == ps.EVENT_AUTHORITY_POLICY
    assert "Generated views match machine state." in registry["owner_label_crosswalk"]["acceptance_text"]
    assert "CI_STATE_DRIFT_MISSING" in registry["owner_label_crosswalk"]["failure_codes"]


def test_exact_crosswalk_and_event_policy_poisons_fail_closed() -> None:
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    poisons = []
    item = copy.deepcopy(registry)
    item["p5_000_crosswalk"]["rows"][0]["board_items"][0]["board_id"] = "P9.999"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["p5_000_crosswalk"]["rows"][1]["board_items"][0]["failure_code"] = "bad-code"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["p5_000_crosswalk"]["rows"][1] = copy.deepcopy(item["p5_000_crosswalk"]["rows"][0])
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["owner_label_crosswalk"]["acceptance_text"] = ["fabricated"] * 9
    poisons.append(item)
    item = copy.deepcopy(registry)
    left = item["p5_000_crosswalk"]["rows"][0]["board_items"][0]
    right = item["p5_000_crosswalk"]["rows"][1]["board_items"][0]
    left["acceptance_text"], right["acceptance_text"] = right["acceptance_text"], left["acceptance_text"]
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["event_authority_policy"]["history_mode"] = "ALL_PARENTS"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["surfaces"][0]["drift_risk"] = "MUTATED_POLICY"
    poisons.append(item)
    schema = load("docs/semantic_quarantine/SINGLE_MACHINE_STATE_SCHEMA_v1.json")
    for item in poisons:
        with pytest.raises(ps.StateError, match="STATE_SCHEMA_INVALID"):
            ps.validate_schema(item, schema)


def test_inventory_rejects_new_unregistered_status_surface() -> None:
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    for path in ("NEW_CURRENT_STATUS.md", "NEW-STATUS.md", "NEW STATUS.md", "docs/NEW-CURRENT.md", "docs/routeB_bus/999-CURRENT-STATUS.md"):
        with pytest.raises(ps.StateError, match="STATUS_SURFACE_INVENTORY_INCOMPLETE"):
            ps.validate_registry(registry, [path])


def test_prospective_inventory_includes_every_new_p5_path() -> None:
    tracked = set(ps.tracked_paths(ROOT))
    assert ps.P5_PROSPECTIVE_PATHS <= tracked
    assert "docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json" in {
        row["path"] for row in load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")["surfaces"]
    }


@pytest.mark.parametrize(
    "path",
    [
        "ACTIVE/SESSION_ENTRY.md",
        "docs/routeB_bus/999_NEW_CURRENT_STATUS.md",
        "docs/routeB_bus/ACTIVE_QUEUE.md",
        "docs/routeB_bus/NEXT_ACTION.md",
        "docs/routeB_bus/NewCurrent.md",
        "docs/routeB_bus/999_new.goal.md",
    ],
)
def test_sensitive_future_status_seeds_require_exact_registry_rows(path: str) -> None:
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    with pytest.raises(ps.StateError, match="STATUS_SURFACE_INVENTORY_INCOMPLETE"):
        ps.validate_registry(registry, [path])


def test_historical_monitor_cannot_select_work() -> None:
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    poisoned = copy.deepcopy(registry)
    monitor = next(row for row in poisoned["surfaces"] if row["role"] == "HISTORICAL")
    monitor["selector_effect"] = "ACTIVE"
    with pytest.raises(ps.StateError, match="STALE_MONITOR_SELECTED_WORK"):
        ps.validate_registry(poisoned, [])


def test_selected_goal_requires_exact_component_state_registry_row() -> None:
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    execution = load("orchestrator/state/PROJECT_EXECUTION_STATE.json")
    poisoned = copy.deepcopy(registry)
    selected = next(row for row in poisoned["surfaces"] if row["path"] == execution["selector"]["selected_goal_path"])
    selected["role"] = "HISTORICAL"
    selected["selector_effect"] = "NONE"
    with pytest.raises(ps.StateError, match="STATE_AUTHORITY_AMBIGUOUS"):
        ps.validate_selector_registry(execution, poisoned)


@pytest.mark.parametrize(
    ("target", "key", "value"),
    [
        ("facts", "selector", {"selected_goal_id": "999"}),
        ("execution", "public_claims", {"unconditional_rh_proof": True}),
    ],
)
def test_fact_and_execution_stores_cannot_be_conflated(target: str, key: str, value: object) -> None:
    facts = load("orchestrator/state/PROJECT_FACTS.json")
    execution = load("orchestrator/state/PROJECT_EXECUTION_STATE.json")
    (facts if target == "facts" else execution)[key] = value
    with pytest.raises(ps.StateError, match="FACT_STATE_CONFLATION"):
        ps.validate_store_separation(facts, execution)


def test_generated_view_drift_plant_is_detected() -> None:
    with pytest.raises(ps.StateError, match="GENERATED_VIEW_DRIFT_UNDETECTED"):
        ps.assert_generated_content("manual edit", "generated bytes", "README.md")


def test_generated_headers_pin_all_project_state_sources() -> None:
    state = load("orchestrator/state/PROJECT_STATE.json")
    manifest_sha = ps.sha256(ROOT / "orchestrator/state/PROJECT_STATE.json")
    views = ps.render_views(state, manifest_sha)
    for content in views.values():
        assert "project_state_sha256:" in content
        assert "facts_sha256:" in content
        assert "execution_sha256:" in content
        assert "events_sha256:" in content
        assert "event_tail_sha256:" in content
        assert "schema_sha256:" in content
        assert "builder_program_sha256:" in content
        assert "selector_program_sha256:" in content
    assert "PUBLIC_EXPORT_INDEX_AND_AXIOM_RECEIPT_v1.md" in views["docs/generated/PROJECT_STATUS.md"]


def test_event_hash_chain_rejects_retroactive_edit(tmp_path: Path) -> None:
    source = ROOT / "orchestrator/state/PROJECT_STATE_EVENTS.jsonl"
    event_file = tmp_path / "events.jsonl"
    event_file.write_bytes(source.read_bytes().replace(b"P5 single", b"P5 altered"))
    with pytest.raises(ps.StateError, match="EVENT_HASH_INVALID"):
        ps.load_events(event_file)


@pytest.mark.parametrize(("field", "value"), [("event_id", 7), ("kind", "bad-kind"), ("summary", None), ("recorded_at", "2026-08-27T12:00:00")])
def test_event_shape_rejects_malformed_rehashed_values(tmp_path: Path, field: str, value: object) -> None:
    event = json.loads((ROOT / "orchestrator/state/PROJECT_STATE_EVENTS.jsonl").read_text(encoding="utf-8"))
    event[field] = value
    payload = dict(event)
    payload.pop("event_sha256")
    event["event_sha256"] = hashlib.sha256(ps.canonical_json(payload)).hexdigest()
    path = tmp_path / "events.jsonl"
    path.write_text(json.dumps(event, separators=(",", ":")) + "\n", encoding="utf-8")
    with pytest.raises(ps.StateError, match="EVENT_SCHEMA_INVALID"):
        ps.load_events(path)


def test_event_ids_are_unique(tmp_path: Path) -> None:
    path = tmp_path / "events.jsonl"
    path.write_bytes((ROOT / "orchestrator/state/PROJECT_STATE_EVENTS.jsonl").read_bytes())
    original_id = json.loads(path.read_text(encoding="utf-8"))["event_id"]
    append_valid_event(path, original_id, "duplicate id")
    with pytest.raises(ps.StateError, match="EVENT_SCHEMA_INVALID"):
        ps.load_events(path)


def test_event_prefix_rejects_edit_reorder_or_removal() -> None:
    old = b"event-one\nevent-two\n"
    for changed in (b"event-zero\n" + old, b"event-two\nevent-one\n", b"event-one\n"):
        with pytest.raises(ps.StateError, match="RETROACTIVE_STATE_REPAIR"):
            ps.ensure_append_only(old, changed)
    ps.ensure_append_only(old, old + b"event-three\n")


def test_committed_event_history_rejects_rewrite_and_rehash(tmp_path: Path) -> None:
    event_dir = tmp_path / "orchestrator/state"
    event_dir.mkdir(parents=True)
    event_path = event_dir / "PROJECT_STATE_EVENTS.jsonl"
    original = json.loads((ROOT / "orchestrator/state/PROJECT_STATE_EVENTS.jsonl").read_text(encoding="utf-8"))
    event_path.write_text(json.dumps(original, separators=(",", ":")) + "\n", encoding="utf-8")
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "plant@example.invalid"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "P5 plant"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "orchestrator/state/PROJECT_STATE_EVENTS.jsonl"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "bootstrap"], cwd=tmp_path, check=True)
    rewritten = dict(original)
    rewritten["summary"] = "retroactively rewritten history"
    payload = dict(rewritten)
    payload.pop("event_sha256")
    rewritten["event_sha256"] = hashlib.sha256(ps.canonical_json(payload)).hexdigest()
    event_path.write_text(json.dumps(rewritten, separators=(",", ":")) + "\n", encoding="utf-8")
    ps.load_events(event_path)  # internally valid after the attacker rehashes it
    with pytest.raises(ps.StateError, match="RETROACTIVE_STATE_REPAIR"):
        ps.check_event_append_only(tmp_path)


def append_valid_event(path: Path, event_id: str, summary: str) -> None:
    previous = json.loads(path.read_text(encoding="utf-8").splitlines()[-1])
    event = {
        "schema": "q3_project_state_event.v1",
        "event_id": event_id,
        "recorded_at": "2026-08-27T12:00:00+02:00",
        "kind": "TEST_APPEND",
        "summary": summary,
        "prev_event_sha256": previous["event_sha256"],
    }
    event["event_sha256"] = hashlib.sha256(ps.canonical_json(event)).hexdigest()
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(event, separators=(",", ":")) + "\n")


def test_first_parent_merge_contract_accepts_main_and_rejects_rewrite(tmp_path: Path) -> None:
    event_dir = tmp_path / "orchestrator/state"
    event_dir.mkdir(parents=True)
    event_path = event_dir / "PROJECT_STATE_EVENTS.jsonl"
    event_path.write_bytes((ROOT / "orchestrator/state/PROJECT_STATE_EVENTS.jsonl").read_bytes())
    subprocess.run(["git", "init", "-qb", "main"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "plant@example.invalid"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "P5 plant"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "orchestrator/state/PROJECT_STATE_EVENTS.jsonl"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "bootstrap"], cwd=tmp_path, check=True)

    subprocess.run(["git", "checkout", "-qb", "side"], cwd=tmp_path, check=True)
    append_valid_event(event_path, "SIDE", "valid side append")
    side_bytes = event_path.read_bytes()
    subprocess.run(["git", "add", "orchestrator/state/PROJECT_STATE_EVENTS.jsonl"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "side append"], cwd=tmp_path, check=True)

    subprocess.run(["git", "checkout", "-q", "main"], cwd=tmp_path, check=True)
    append_valid_event(event_path, "MAIN", "project-authoritative main append")
    subprocess.run(["git", "add", "orchestrator/state/PROJECT_STATE_EVENTS.jsonl"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "main append"], cwd=tmp_path, check=True)
    subprocess.run(["git", "merge", "-q", "-s", "ours", "side", "-m", "acceptable merge"], cwd=tmp_path, check=True)
    ps.check_event_append_only(tmp_path)

    event_path.write_bytes(side_bytes)
    subprocess.run(["git", "add", "orchestrator/state/PROJECT_STATE_EVENTS.jsonl"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "malicious merge result"], cwd=tmp_path, check=True)
    with pytest.raises(ps.StateError, match="RETROACTIVE_STATE_REPAIR"):
        ps.check_event_append_only(tmp_path)


def test_execution_selector_matches_physical_goal_runtime() -> None:
    execution = load("orchestrator/state/PROJECT_EXECUTION_STATE.json")
    assert execution["selector"] == ps.read_live_selector(ROOT)


def test_scoped_precedence_and_routeb_conflict_fail_closed() -> None:
    execution = load("orchestrator/state/PROJECT_EXECUTION_STATE.json")
    ps.validate_scoped_precedence(ROOT, execution)
    poisoned = copy.deepcopy(execution)
    project = next(row for row in poisoned["authority_domains"] if row["domain"] == "PROJECT_GOAL_SELECTION")
    project["authority_order"] = ["PROJECT_EXECUTION_STATE", "PHYSICAL_BUS"]
    with pytest.raises(ps.StateError, match="STATE_AUTHORITY_AMBIGUOUS"):
        ps.validate_scoped_precedence(ROOT, poisoned)


def test_active_selector_set_is_closed() -> None:
    execution = load("orchestrator/state/PROJECT_EXECUTION_STATE.json")
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    ps.validate_selector_registry(execution, registry)
    extra = copy.deepcopy(registry)
    extra["surfaces"].append({
        "path": "TASK.md", "role": "SELECTOR", "selector_effect": "ACTIVE",
        "source_store": "POISON", "consumers": [], "drift_risk": "POISON",
    })
    with pytest.raises(ps.StateError, match="closed ACTIVE selector set"):
        ps.validate_selector_registry(execution, extra)
    missing = copy.deepcopy(registry)
    next(row for row in missing["surfaces"] if row["path"] == "docs/Codex/CURRENT.md")["selector_effect"] = "NONE"
    with pytest.raises(ps.StateError, match="closed ACTIVE selector set"):
        ps.validate_selector_registry(execution, missing)


def test_exact_component_map_rejects_id_swap_and_task_substitution() -> None:
    execution = load("orchestrator/state/PROJECT_EXECUTION_STATE.json")
    swapped = copy.deepcopy(execution)
    swapped["component_states"][0]["id"], swapped["component_states"][1]["id"] = (
        swapped["component_states"][1]["id"], swapped["component_states"][0]["id"]
    )
    with pytest.raises(ps.StateError, match="STATE_SCHEMA_INVALID"):
        ps.validate_document_shape(swapped)
    substituted = copy.deepcopy(execution)
    codex = next(row for row in substituted["component_states"] if row["id"] == "CODEX_CURRENT")
    codex["path"] = "TASK.md"
    with pytest.raises(ps.StateError, match="exact component map"):
        ps.validate_document_shape(substituted)


def test_malformed_nested_documents_fail_as_state_error() -> None:
    facts = load("orchestrator/state/PROJECT_FACTS.json")
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    malformed = []
    item = copy.deepcopy(facts)
    item["public_claims"] = 7
    malformed.append(item)
    item = copy.deepcopy(registry)
    item["surfaces"][0] = 7
    malformed.append(item)
    for item in malformed:
        with pytest.raises(ps.StateError, match="STATE_SCHEMA_INVALID"):
            ps.validate_document_shape(item)


def alias_fixture(tmp_path: Path, mode: str = "valid") -> tuple[dict, dict, set[str]]:
    canonical = tmp_path / "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md"
    canonical.parent.mkdir(parents=True)
    if mode != "canonical_missing":
        canonical.write_text("canonical router\n", encoding="utf-8")
    (tmp_path / "ACTIVE").symlink_to("q3.lean.aristotle/ACTIVE", target_is_directory=True)
    alias = tmp_path / "SESSION_ENTRY.md"
    if mode == "regular_divergent":
        alias.write_text("divergent copy\n", encoding="utf-8")
    elif mode == "wrong_target":
        alias.symlink_to("q3.lean.aristotle/ACTIVE/WRONG.md")
    else:
        alias.symlink_to("ACTIVE/SESSION_ENTRY.md")
    execution = load("orchestrator/state/PROJECT_EXECUTION_STATE.json")
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    tracked = {"ACTIVE", "SESSION_ENTRY.md", "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md"}
    return execution, registry, tracked


def test_session_entry_alias_invariant_accepts_exact_layout(tmp_path: Path) -> None:
    execution, registry, tracked = alias_fixture(tmp_path)
    ps.validate_session_entry_alias(tmp_path, execution, registry, tracked=tracked)


@pytest.mark.parametrize("mode", ["regular_divergent", "wrong_target", "canonical_missing"])
def test_session_entry_alias_invariant_rejects_filesystem_poison(tmp_path: Path, mode: str) -> None:
    execution, registry, tracked = alias_fixture(tmp_path, mode)
    with pytest.raises(ps.StateError, match="STATE_AUTHORITY_AMBIGUOUS"):
        ps.validate_session_entry_alias(tmp_path, execution, registry, tracked=tracked)


def test_session_entry_alias_invariant_rejects_unrepresented_canonical_selector(tmp_path: Path) -> None:
    execution, registry, tracked = alias_fixture(tmp_path)
    execution["component_states"] = [
        row for row in execution["component_states"]
        if row.get("path") != "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md"
    ]
    with pytest.raises(ps.StateError, match="STATE_AUTHORITY_AMBIGUOUS"):
        ps.validate_session_entry_alias(tmp_path, execution, registry, tracked=tracked)
    poisoned = copy.deepcopy(execution)
    poisoned["selector"]["selected_goal_id"] = "999"
    with pytest.raises(ps.StateError, match="STATE_AUTHORITY_AMBIGUOUS"):
        ps.validate_scoped_precedence(ROOT, poisoned)


def test_authoritative_state_excludes_foreign_worktree_bytes() -> None:
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    state = load("orchestrator/state/PROJECT_STATE.json")
    referenced = {
        item["path"] for item in state["source_hashes"].values()
    } | {item["path"] for item in state["component_hashes"]}
    denylist = registry["foreign_worktree_denylist"]
    assert referenced.isdisjoint(denylist["exact_paths"])
    assert len(denylist["exact_paths"]) == 6
    assert denylist["glob_patterns"] == ["orchestrator/state/*.db"]
    with pytest.raises(ps.StateError, match="FOREIGN_WORKTREE_FILE_TRACKED"):
        ps.validate_registry(registry, ["orchestrator/state/future.db"])


def test_component_hash_drift_changes_authoritative_projection(tmp_path: Path) -> None:
    state = load("orchestrator/state/PROJECT_STATE.json")
    component = state["component_hashes"][0]
    original = ROOT / component["path"]
    changed = tmp_path / "component"
    changed.write_bytes(original.read_bytes() + b"\n")
    assert ps.sha256(changed) != component["sha256"]


def test_control_schema_and_programs_are_source_hashed() -> None:
    state = load("orchestrator/state/PROJECT_STATE.json")
    expected = {
        "schema": "docs/semantic_quarantine/SINGLE_MACHINE_STATE_SCHEMA_v1.json",
        "builder_program": "orchestrator/project_state.py",
        "selector_program": "orchestrator/goal_runtime.py",
    }
    for key, path in expected.items():
        assert state["source_hashes"][key] == {"path": path, "sha256": ps.sha256(ROOT / path)}


def test_fact_receipt_contract_rejects_missing_duplicate_and_swapped_hashes() -> None:
    facts = load("orchestrator/state/PROJECT_FACTS.json")
    schema = load("docs/semantic_quarantine/SINGLE_MACHINE_STATE_SCHEMA_v1.json")
    duplicate = copy.deepcopy(facts)
    duplicate["receipts"][1] = copy.deepcopy(duplicate["receipts"][0])
    with pytest.raises(ps.StateError, match="receipt contract"):
        ps.validate_schema(duplicate, schema)
    missing = copy.deepcopy(facts)
    missing["receipts"] = missing["receipts"][:1]
    with pytest.raises(ps.StateError, match="receipts"):
        ps.validate_schema(missing, schema)
    swapped = copy.deepcopy(facts)
    swapped["receipts"][0]["sha256"], swapped["receipts"][1]["sha256"] = (
        swapped["receipts"][1]["sha256"], swapped["receipts"][0]["sha256"]
    )
    with pytest.raises(ps.StateError, match="FACT_RECEIPT_DRIFT"):
        ps.validate_fact_receipts(ROOT, swapped)


def schema_accepts_builtin(document: dict) -> bool:
    try:
        ps.validate_document_shape(document)
    except ps.StateError:
        return False
    return True


def schema_accepts_jsonschema(document: dict, schema: dict) -> bool:
    return not list(jsonschema.Draft202012Validator(schema).iter_errors(document))


def test_builtin_and_jsonschema_share_closed_poison_corpus() -> None:
    schema = load("docs/semantic_quarantine/SINGLE_MACHINE_STATE_SCHEMA_v1.json")
    facts = load("orchestrator/state/PROJECT_FACTS.json")
    execution = load("orchestrator/state/PROJECT_EXECUTION_STATE.json")
    registry = load("docs/semantic_quarantine/STATUS_SURFACE_REGISTRY_v1.json")
    good = [facts, execution, registry, load("orchestrator/state/PROJECT_STATE.json")]
    poisons: list[dict] = []

    item = copy.deepcopy(facts)
    item["receipts"][0]["path"] = "/absolute/receipt.md"
    poisons.append(item)
    item = copy.deepcopy(facts)
    item["receipts"][0]["path"] = 17
    poisons.append(item)
    for path in ("./a", "a/../b", "a/./b", "a//b", "a\\b"):
        item = copy.deepcopy(facts)
        item["receipts"][0]["path"] = path
        poisons.append(item)
    item = copy.deepcopy(facts)
    item["receipts"][0]["sha256"] = "not-a-sha"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["owner_label_crosswalk"]["owner_label"] = "P5"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["p5_000_crosswalk"]["rows"][0]["extra"] = True
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["surfaces"][0]["role"] = "UNKNOWN"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["surfaces"][0]["drift_risk"] = "MUTATED_POLICY"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["coverage_rules"][0]["path_prefix"] = "/"
    poisons.append(item)
    for prefix in ("a/./", "./a/", "a//b/", "docs/", "q3.lean.aristotle/"):
        item = copy.deepcopy(registry)
        item["coverage_rules"][0]["path_prefix"] = prefix
        poisons.append(item)
    item = copy.deepcopy(registry)
    item["coverage_rules"][0]["extra"] = True
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["foreign_worktree_denylist"]["exact_paths"][0] = "/absolute/foreign"
    poisons.append(item)
    for denylist in ([], "abc"):
        item = copy.deepcopy(registry)
        item["foreign_worktree_denylist"] = denylist
        poisons.append(item)
    item = copy.deepcopy(registry)
    item["foreign_worktree_denylist"]["exact_paths"][1] = item["foreign_worktree_denylist"]["exact_paths"][0]
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["foreign_worktree_denylist"]["glob_patterns"] = ["*"]
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["owner_label_crosswalk"]["acceptance_text"] = "not-an-array"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["owner_label_crosswalk"]["failure_codes"] = "NOT_AN_ARRAY"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["coverage_rules"][0]["exception_paths"] = "not-an-array"
    poisons.append(item)
    item = copy.deepcopy(registry)
    item["coverage_rules"][0]["exception_paths"] = ["a/../b"]
    poisons.append(item)
    item = copy.deepcopy(load("orchestrator/state/PROJECT_STATE.json"))
    item["projection"]["selected_goal_id"] = 58
    poisons.append(item)
    item = copy.deepcopy(execution)
    item["component_states"][1]["id"] = item["component_states"][0]["id"]
    poisons.append(item)
    item = copy.deepcopy(execution)
    item["component_states"][1]["path"] = "TASK.md"
    poisons.append(item)
    item = copy.deepcopy(execution)
    item["component_states"][1]["role"] = "SCOPED_SELECTOR"
    poisons.append(item)
    item = copy.deepcopy(execution)
    physical = next(row for row in item["component_states"] if row["id"] == "PHYSICAL_BUS_GOAL")
    physical["path"] = "docs/routeB_bus/999_poison.goal.md"
    poisons.append(item)
    item = copy.deepcopy(execution)
    item["authority_domains"][0]["component_ids"] = ["CODEX_CURRENT"]
    poisons.append(item)
    item = copy.deepcopy(execution)
    item["authority_domains"][0]["authority_order"] = ["PROJECT_EXECUTION_STATE"]
    poisons.append(item)
    item = copy.deepcopy(execution)
    project = next(row for row in item["authority_domains"] if row["domain"] == "PROJECT_GOAL_SELECTION")
    project["current_status"] = "SELECT_EXACT_GOAL_999"
    poisons.append(item)
    item = copy.deepcopy(execution)
    codex = next(row for row in item["authority_domains"] if row["domain"] == "CODEX_TASK_SELECTION")
    codex["current_status"] = "ACTIVE"
    poisons.append(item)
    item = copy.deepcopy(execution)
    item["selector"]["selected_goal_id"] = 999
    poisons.append(item)

    for document in good:
        assert schema_accepts_builtin(document)
        assert schema_accepts_jsonschema(document, schema)
    for document in poisons:
        assert not schema_accepts_builtin(document)
        assert not schema_accepts_jsonschema(document, schema)
