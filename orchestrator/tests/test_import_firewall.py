from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "import_firewall", ROOT / "orchestrator/import_firewall.py"
)
assert SPEC and SPEC.loader
firewall = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = firewall
SPEC.loader.exec_module(firewall)


def load(path: str) -> dict:
    return json.loads((ROOT / path).read_text(encoding="utf-8"))


def exact_rule(module: str, path: str, module_class: str) -> dict:
    return {
        "id": module.lower().replace(".", "_"),
        "artifact_kind": "LEAN_MODULE",
        "identity": {
            "source_root": "q3.lean.aristotle",
            "repo_relative_path": path,
            "lean_module": module,
        },
        "module_class": module_class,
        "lifecycle_status": "CANDIDATE",
        "traits": [],
    }


def registry(*rules: dict, prefixes: list[dict] | None = None) -> dict:
    return {"rules": {"exact": list(rules), "prefix": prefixes or []}}


def live_inputs() -> tuple[dict, dict, dict]:
    return firewall.load_inputs()


def test_policy_is_the_exact_closed_contract() -> None:
    policy, _registry, _schema = live_inputs()
    firewall.validate_policy(policy)
    poisons = []
    for key, value in (
        ("public_root_class", "LEGACY"),
        ("forbidden_public_target_classes", ["LEGACY"]),
        ("required_plants", ["PUBLIC_IMPORTS_LEGACY_MODULE"]),
        ("positive_controls", ["CURRENT_PUBLIC_CANONICAL_SLICE"]),
    ):
        poisoned = copy.deepcopy(policy)
        poisoned[key] = value
        poisons.append(poisoned)
    poisoned = copy.deepcopy(policy)
    poisoned["semantic_declaration_audit"]["mixed_module_rule"] = "ALLOW"
    poisons.append(poisoned)
    for poisoned in poisons:
        with pytest.raises(firewall.FirewallError, match="IMPORT_FIREWALL_POLICY_INVALID"):
            firewall.validate_policy(poisoned)


def test_registry_and_schema_validate_current_contract() -> None:
    _policy, current_registry, schema = live_inputs()
    firewall.validate_registry(current_registry, schema)


def test_parser_accepts_supported_lean_import_comments() -> None:
    source = """/- header /- nested -/ comment -/
import Q3.Basic.Defs /- inline -/
import Q3.Basic.WeilSquareClass -- line comment
"""
    assert firewall.imports_from_text(source, source="plant.lean") == [
        "Q3.Basic.Defs",
        "Q3.Basic.WeilSquareClass",
    ]


@pytest.mark.parametrize(
    "source",
    [
        "import Q3.Basic.Defs Q3.Hidden\n",
        "import\n",
        "public import Q3.Basic.Defs extra\n",
    ],
)
def test_parser_fails_closed_on_unparsed_import_forms(source: str) -> None:
    with pytest.raises(firewall.FirewallError, match="UNPARSED_IMPORT"):
        firewall.imports_from_text(source, source="plant.lean")


def test_parser_fails_closed_on_unterminated_nested_comment() -> None:
    with pytest.raises(firewall.FirewallError, match="UNTERMINATED_LEAN_COMMENT"):
        firewall.imports_from_text("/- open\nimport Q3.Hidden\n", source="plant.lean")


def test_public_roots_include_prefix_classified_modules() -> None:
    policy, _current_registry, _schema = live_inputs()
    prefix = {
        "id": "public_prefix",
        "artifact_kind": "LEAN_MODULE",
        "match": {
            "source_root": "q3.lean.aristotle",
            "repo_relative_path_prefix": "synthetic/Public/",
            "lean_module_prefix": "Synthetic.Public.",
        },
        "module_class": "PUBLIC_CANONICAL",
        "lifecycle_status": "CANDIDATE",
        "traits": [],
    }
    paths = {"Synthetic.Public.Future": "synthetic/Public/Future.lean"}
    graph = firewall.build_graph(
        policy,
        registry(prefixes=[prefix]),
        module_paths=paths,
        source_texts={paths["Synthetic.Public.Future"]: ""},
    )
    assert graph["public_roots"] == ["Synthetic.Public.Future"]


def test_forbidden_class_edge_plant_uses_production_graph_path() -> None:
    policy, _registry, _schema = live_inputs()
    assert firewall.run_import_edge_plant(policy) == {
        "plant": "PUBLIC_IMPORTS_LEGACY_MODULE",
        "status": "REJECTED",
    }


def test_unclassified_reachable_local_module_is_rejected() -> None:
    policy, _registry, _schema = live_inputs()
    public = exact_rule("Synthetic.Public", "synthetic/Public.lean", "PUBLIC_CANONICAL")
    paths = {
        "Synthetic.Public": "synthetic/Public.lean",
        "Synthetic.Hidden": "synthetic/Hidden.lean",
    }
    sources = {
        "synthetic/Public.lean": "import Synthetic.Hidden\n",
        "synthetic/Hidden.lean": "",
    }
    with pytest.raises(firewall.FirewallError, match="PUBLIC_REACHABILITY_UNCLASSIFIED"):
        firewall.build_graph(policy, registry(public), module_paths=paths, source_texts=sources)


def test_untracked_on_disk_local_module_is_discovered(tmp_path: Path, monkeypatch) -> None:
    root = tmp_path / "repo"
    source_root = root / "q3.lean.aristotle"
    candidate = source_root / "Q3/Hidden.lean"
    candidate.parent.mkdir(parents=True)
    candidate.write_text("", encoding="utf-8")
    monkeypatch.setattr(firewall, "REPO", root)
    monkeypatch.setattr(firewall, "tracked_lean_modules", lambda _source_root: {})
    assert firewall.local_lean_modules("q3.lean.aristotle") == {
        "Q3.Hidden": "q3.lean.aristotle/Q3/Hidden.lean"
    }


def test_missing_exact_public_root_is_rejected() -> None:
    policy, _registry, _schema = live_inputs()
    rules = registry(
        exact_rule("Synthetic.Live", "synthetic/Live.lean", "PUBLIC_CANONICAL"),
        exact_rule("Synthetic.Missing", "synthetic/Missing.lean", "PUBLIC_CANONICAL"),
    )
    with pytest.raises(firewall.FirewallError, match="PUBLIC_CANONICAL_MODULE_MISSING"):
        firewall.build_graph(
            policy,
            rules,
            module_paths={"Synthetic.Live": "synthetic/Live.lean"},
            source_texts={"synthetic/Live.lean": ""},
        )


def test_local_namespace_typo_is_not_treated_as_external() -> None:
    policy, _registry, _schema = live_inputs()
    public = exact_rule("Synthetic.Public", "synthetic/Public.lean", "PUBLIC_CANONICAL")
    with pytest.raises(firewall.FirewallError, match="IMPORT_GRAPH_LOCAL_MODULE_MISSING"):
        firewall.build_graph(
            policy,
            registry(public),
            module_paths={"Synthetic.Public": "synthetic/Public.lean"},
            source_texts={"synthetic/Public.lean": "import Synthetic.Typo\n"},
        )


def test_exact_prefix_overlap_is_rejected() -> None:
    policy, _registry, _schema = live_inputs()
    exact = exact_rule("Synthetic.Public", "synthetic/Public.lean", "PUBLIC_CANONICAL")
    prefix = {
        "id": "legacy_prefix",
        "artifact_kind": "LEAN_MODULE",
        "match": {
            "source_root": "q3.lean.aristotle",
            "repo_relative_path_prefix": "synthetic/",
            "lean_module_prefix": "Synthetic.",
        },
        "module_class": "LEGACY",
        "lifecycle_status": "COMPATIBILITY_ONLY",
        "traits": [],
    }
    with pytest.raises(firewall.FirewallError, match="MODULE_CLASS_AMBIGUOUS"):
        firewall.build_graph(
            policy,
            registry(exact, prefixes=[prefix]),
            module_paths={"Synthetic.Public": "synthetic/Public.lean"},
            source_texts={"synthetic/Public.lean": ""},
        )


def test_public_roots_are_built_before_semantic_environment_use(monkeypatch) -> None:
    policy, _registry, _schema = live_inputs()
    calls = []

    def fake_run(command, **kwargs):
        calls.append((command, kwargs))
        return subprocess.CompletedProcess(command, 0, "built", "")

    monkeypatch.setattr(firewall.subprocess, "run", fake_run)
    graph = {"public_roots": ["Synthetic.A", "Synthetic.B"]}
    assert firewall.build_public_roots(graph, policy) == {
        "roots": ["Synthetic.A", "Synthetic.B"],
        "status": "PASS",
    }
    assert calls[0][0] == ["lake", "build", "Synthetic.A", "Synthetic.B"]
    assert "LD_LIBRARY_PATH" not in calls[0][1]["env"]


def test_allowed_transitive_graph_is_complete_and_deterministic() -> None:
    policy, _registry, _schema = live_inputs()
    rules = registry(
        exact_rule("Synthetic.Public", "synthetic/Public.lean", "PUBLIC_CANONICAL"),
        exact_rule("Synthetic.Shared", "synthetic/Shared.lean", "CORE_SHARED"),
        exact_rule("Synthetic.Core", "synthetic/Core.lean", "CORE_SHARED"),
    )
    paths = {
        "Synthetic.Public": "synthetic/Public.lean",
        "Synthetic.Shared": "synthetic/Shared.lean",
        "Synthetic.Core": "synthetic/Core.lean",
    }
    sources = {
        "synthetic/Public.lean": "import Synthetic.Shared\nimport Mathlib\n",
        "synthetic/Shared.lean": "import Synthetic.Core\n",
        "synthetic/Core.lean": "",
    }
    first = firewall.build_graph(policy, rules, module_paths=paths, source_texts=sources)
    second = firewall.build_graph(
        policy,
        rules,
        module_paths=dict(reversed(list(paths.items()))),
        source_texts=sources,
    )
    assert first == second
    assert [row["module"] for row in first["reachable_modules"]] == [
        "Synthetic.Core",
        "Synthetic.Public",
        "Synthetic.Shared",
    ]
    assert first["external_imports"] == [{"source": "Synthetic.Public", "target": "Mathlib"}]
    assert (
        hashlib.sha256(firewall.canonical_json(first)).hexdigest()
        == hashlib.sha256(firewall.canonical_json(second)).hexdigest()
    )


def test_mixed_module_forbidden_overrides_are_exact() -> None:
    policy, current_registry, _schema = live_inputs()
    forbidden, mixed = firewall.forbidden_declarations(
        current_registry,
        policy,
        {"Q3.Basic.Defs", "Q3.Basic.WeilSquareClass", "Q3.Basic.WeilDirectRoute"},
    )
    assert forbidden == ["Q3.W_K", "Q3.W_K_subset_Weil_cone_K", "Q3.Weil_cone", "Q3.Weil_cone_K"]
    assert mixed == ["Q3.Basic.Defs"]


def test_semantic_leak_plant_and_current_environment_audit() -> None:
    policy, current_registry, _schema = live_inputs()
    graph = firewall.build_graph(policy, current_registry)
    positive = firewall.run_semantic_audit(graph, current_registry, policy)
    direct = firewall.run_semantic_audit(graph, current_registry, policy, plant="DIRECT_VALUE")
    transitive = firewall.run_semantic_audit(
        graph, current_registry, policy, plant="TRANSITIVE_VALUE"
    )
    type_use = firewall.run_semantic_audit(graph, current_registry, policy, plant="TYPE")
    assert positive["status"] == "PASS"
    assert positive["checked_declarations"] >= positive["public_declarations"] > 0
    assert direct == {"plant": "PUBLIC_DECLARATION_USES_LEGACY_OVERRIDE", "status": "REJECTED"}
    assert transitive == {
        "plant": "PUBLIC_TRANSITIVE_DECLARATION_USES_LEGACY_OVERRIDE",
        "status": "REJECTED",
    }
    assert type_use == {"plant": "PUBLIC_TYPE_USES_LEGACY_OVERRIDE", "status": "REJECTED"}


def test_receipt_is_current_pinned_and_excludes_foreign_worktree_paths() -> None:
    expected = firewall.build_receipt()
    actual = load("docs/semantic_quarantine/IMPORT_FIREWALL_RECEIPT_v1.json")
    assert actual == expected
    assert expected["inputs"]["checker"]["path"] == "orchestrator/import_firewall.py"
    assert expected["inputs"]["lean_toolchain"]["path"] == "q3.lean.aristotle/lean-toolchain"
    assert expected["inputs"]["launcher"]["path"] == "scripts/check_import_firewall.sh"
    assert expected["inputs"]["python_project"]["path"] == "pyproject.toml"
    assert expected["inputs"]["python_lock"]["path"] == "uv.lock"
    assert expected["inputs"]["lakefile"]["path"] == "q3.lean.aristotle/lakefile.toml"
    assert expected["inputs"]["lake_manifest"]["path"] == "q3.lean.aristotle/lake-manifest.json"
    serialized = json.dumps(expected, sort_keys=True)
    assert "docs/routeB_bus/mythos/" not in serialized
    assert "orchestrator/state/*.db" not in serialized


def test_duplicate_json_keys_fail_closed(tmp_path: Path) -> None:
    path = tmp_path / "duplicate.json"
    path.write_text('{"schema": 1, "schema": 2}\n', encoding="utf-8")
    with pytest.raises(firewall.FirewallError, match="DUPLICATE_JSON_KEY"):
        firewall.load_json(path)


def test_current_public_graph_has_no_forbidden_class_edge() -> None:
    policy, current_registry, _schema = live_inputs()
    graph = firewall.build_graph(policy, current_registry)
    forbidden = set(policy["forbidden_public_target_classes"])
    assert graph["public_roots"] == ["Q3.Basic.WeilDirectRoute", "Q3.Basic.WeilSquareClass"]
    assert not any(row["target_class"] in forbidden for row in graph["local_edges"])
