from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

import pytest

from orchestrator import lean_dependency_runtime as runtime

REPO = Path(__file__).resolve().parents[2]
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
UNICODE_PRIVATE_NAME = (
    "_private.Q3.Proofs.RouteB.D0Mode4FiniteBlockInertiaAdditivity.0."
    "mode4HermitianBlock_negativeCount_eq_schur_of_posDef₂₂"
)


def fingerprint(value: int) -> dict[str, str]:
    return {"algorithm": runtime.EXPR_FINGERPRINT_ALGORITHM, "value": str(value)}


def graph_row(
    name: str,
    *,
    type_refs: tuple[str, ...] = (),
    value_refs: tuple[str, ...] = (),
    module: str = "Q3.Plant",
) -> dict[str, object]:
    return {
        "kind": "GRAPH",
        "name": name,
        "module": module,
        "direct_refs": [*type_refs, *value_refs],
        "type_refs": list(type_refs),
        "value_refs": list(value_refs),
    }


def metadata_row(
    name: str,
    *,
    semantic: bool = False,
    declaration_kind: str = "THEOREM",
    module: str = "Q3.Plant",
) -> dict[str, object]:
    return {
        "kind": "METADATA",
        "name": name,
        "module": module,
        "declaration_kind": declaration_kind,
        "type_fingerprint": fingerprint(abs(hash((name, "type")))),
        "value_fingerprint": fingerprint(abs(hash((name, "value"))))
        if semantic
        else None,
        "axioms": ["Classical.choice"],
    }


def action_receipt(command: list[str], *, stdin: str | None = None) -> dict[str, object]:
    result: dict[str, object] = {
        "command": command,
        "returncode": 0,
        "stdout_sha256": EMPTY_SHA256,
        "stderr_sha256": EMPTY_SHA256,
    }
    if stdin is not None:
        result["stdin_sha256"] = hashlib.sha256(stdin.encode("utf-8")).hexdigest()
    return result


def fake_graph_output(payload: str, module: str = "Q3.Plant") -> str:
    module_payload = json.dumps({"kind": "MODULE", "module": module})
    return (
        f"{runtime.MODULE_ROW_PREFIX}{module_payload}\n"
        f"{runtime.ROW_PREFIX}{payload}"
    )


def make_project(tmp_path: Path) -> Path:
    lean_root = tmp_path / "q3.lean.aristotle"
    (lean_root / "Q3").mkdir(parents=True)
    (lean_root / "lean-toolchain").write_text("leanprover/lean4:v4.26.0\n", encoding="utf-8")
    (lean_root / "lakefile.toml").write_text("name = \"plant\"\n", encoding="utf-8")
    (lean_root / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
    return lean_root


def test_graph_probe_uses_environment_transitive_q3_closure() -> None:
    source = runtime.graph_probe_source(["Q3.Root"])
    assert "env.header.moduleNames.filter" in source
    assert "m.toString.startsWith" in source
    assert "ci.type.getUsedConstants" in source
    assert "value.getUsedConstants" in source
    assert "projectModules.foldl" in source
    assert '"type_refs"' in source
    assert '"value_refs"' in source
    assert "fun pfx =>" in source


def test_metadata_probe_binds_types_values_and_axiom_closure() -> None:
    source = runtime.metadata_probe_source(
        ["Q3.Root"],
        ["Q3.Plant.A", "_private.Q3.Plant.0.Helper"],
        semantic_declarations=["Q3.Plant.A"],
    )
    assert '"type_fingerprint"' in source
    assert '"value_fingerprint"' in source
    assert "hash value" in source
    assert "toString ci.type" not in source
    assert "toString (ci.value?" not in source
    assert "semanticValue?" in source
    assert "String.toName" in source
    assert '"_private.Q3.Plant.0.Helper"' in source
    assert "axiomClosure" in source
    assert "ci.isAxiom" in source


def test_unicode_private_environment_name_survives_graph_to_metadata_encoding() -> None:
    payload = json.dumps(graph_row(UNICODE_PRIVATE_NAME))
    parsed_name = runtime.parse_probe_output(
        f"{runtime.ROW_PREFIX}{payload}", expected_kind="GRAPH"
    )[0]["name"]
    assert runtime._environment_name(parsed_name) == UNICODE_PRIVATE_NAME

    source = runtime.metadata_probe_source(
        ["Q3.Proofs.RouteB.D0Mode4FiniteBlockInertiaAdditivity"],
        [parsed_name],
    )
    assert json.dumps(UNICODE_PRIVATE_NAME) in source
    assert "String.toName" in source


@pytest.mark.parametrize(
    "value",
    [
        "Q3.Bad\n#eval 1",
        "Q3.Bad\rName",
        "Q3.Bad\x00Name",
        "Q3.Bad\u202eName",
        "Q3.Bad\ud800Name",
        "Q3.λ",
        "Q3.00.Private",
        "A" * (runtime.MAX_NAME_UTF8_BYTES + 1),
    ],
)
def test_environment_name_rejects_controls_newlines_and_oversize(value: str) -> None:
    with pytest.raises(runtime.LeanDependencyError, match="INVALID_ENVIRONMENT_NAME"):
        runtime._environment_name(value)


def test_caller_supplied_names_remain_ascii_strict_and_bounded() -> None:
    for value in (
        UNICODE_PRIVATE_NAME,
        "Q3.Root\n#eval 1",
        "Q3.Root; unsafe def injected := 1",
        "Q3.Root\ud800Name",
        "A" * (runtime.MAX_NAME_UTF8_BYTES + 1),
    ):
        with pytest.raises(runtime.LeanDependencyError, match="INVALID_NAME"):
            runtime.graph_probe_source([value])


def test_generated_graph_and_metadata_probes_compile_on_real_lean() -> None:
    graph_output, graph_receipt = runtime._run_source(
        REPO, runtime.graph_probe_source(["Q3.Basic.Defs"]), timeout=120
    )
    graph = runtime.parse_probe_output(graph_output, expected_kind="GRAPH")
    assert runtime.parse_module_output(graph_output) == ["Q3.Basic.Defs"]
    rows = {row["name"]: row for row in graph}
    both = rows["Q3.prime_vec_norm_sq_sum"]
    assert "Q3.prime_vec" in both["type_refs"]
    assert "Q3.prime_vec" in both["value_refs"]

    adjacency = {str(row["name"]): list(row["direct_refs"]) for row in graph}
    paths = runtime._paths_to_targets(adjacency, {"Q3.xi_n._proof_1"})
    assert (
        "Q3.Q",
        "Q3.xi_n._proof_1",
        "Q3.arch_term",
    ) in paths
    assert (
        "Q3.Q",
        "Q3.xi_n._proof_1",
        "Q3.prime_term",
    ) in paths
    assert graph_receipt["returncode"] == 0

    metadata_output, metadata_receipt = runtime._run_source(
        REPO,
        runtime.metadata_probe_source(
            ["Q3.Basic.Defs"],
            ["Q3.prime_vec", "Q3.prime_vec_norm_sq_sum"],
            semantic_declarations=["Q3.prime_vec"],
        ),
        timeout=120,
    )
    metadata = {
        row["name"]: row
        for row in runtime.parse_probe_output(metadata_output, expected_kind="METADATA")
    }
    assert metadata["Q3.prime_vec"]["declaration_kind"] == "DEFINITION"
    assert metadata["Q3.prime_vec"]["value_fingerprint"] is not None
    assert metadata["Q3.prime_vec_norm_sq_sum"]["declaration_kind"] == "THEOREM"
    assert metadata["Q3.prime_vec_norm_sq_sum"]["value_fingerprint"] is None
    assert len(metadata_output) < 2_000
    assert metadata_receipt["returncode"] == 0


def test_parse_probe_output_rejects_missing_or_wrong_rows() -> None:
    payload = json.dumps(graph_row("Q3.Plant.A"))
    assert (
        runtime.parse_probe_output(
            f"noise\n{runtime.ROW_PREFIX}{payload}\n", expected_kind="GRAPH"
        )[0]["name"]
        == "Q3.Plant.A"
    )
    with pytest.raises(runtime.LeanDependencyError, match="OUTPUT_EMPTY"):
        runtime.parse_probe_output("noise", expected_kind="GRAPH")
    with pytest.raises(runtime.LeanDependencyError, match="INVALID_ROW"):
        runtime.parse_probe_output(
            f'{runtime.ROW_PREFIX}{{"kind":"METADATA"}}', expected_kind="GRAPH"
        )
    module_payload = json.dumps({"kind": "MODULE", "module": "Q3.Plant"})
    assert runtime.parse_module_output(
        f"noise\n{runtime.MODULE_ROW_PREFIX}{module_payload}\n"
    ) == ["Q3.Plant"]
    with pytest.raises(runtime.LeanDependencyError, match="MODULE_OUTPUT_EMPTY"):
        runtime.parse_module_output("noise")


def test_snapshot_finds_every_distinct_first_hop_and_surface() -> None:
    graph = [
        graph_row("Q3.Plant.A"),
        graph_row("Q3.Plant.B"),
        graph_row("Q3.Plant.Definition"),
        graph_row(
            "Q3.Plant.DirectBoth",
            type_refs=("Q3.Plant.A",),
            value_refs=("Q3.Plant.A",),
        ),
        graph_row("Q3.Plant.WType", type_refs=("Q3.Plant.A",)),
        graph_row("Q3.Plant.WValue", value_refs=("Q3.Plant.A",)),
        graph_row(
            "Q3.Plant.Transitive",
            type_refs=("Q3.Plant.WType",),
            value_refs=("Q3.Plant.WValue",),
        ),
    ]
    names = [str(row["name"]) for row in graph]
    snapshot = runtime.snapshot_from_rows(
        graph,
        [
            metadata_row(
                name,
                semantic=name == "Q3.Plant.Definition",
                declaration_kind="DEFINITION"
                if name == "Q3.Plant.Definition"
                else "THEOREM",
            )
            for name in names
        ],
        import_modules=["Q3.Plant"],
        target_declarations=["Q3.Plant.A", "Q3.Plant.B"],
        semantic_declarations=["Q3.Plant.Definition"],
    )
    consumptions = {
        (
            row["consumer"],
            row["theorem"],
            row["hypothesis_port"]["surface"],
            row["hypothesis_port"]["direct_reference"],
        ): row
        for row in snapshot["consumptions"]
    }
    direct = consumptions[
        (
            "Q3.Plant.DirectBoth",
            "Q3.Plant.A",
            "ELABORATED_TYPE_AND_VALUE",
            "Q3.Plant.A",
        )
    ]
    assert direct["relation"] == "DIRECT"
    type_path = consumptions[
        (
            "Q3.Plant.Transitive",
            "Q3.Plant.A",
            "ELABORATED_TYPE",
            "Q3.Plant.WType",
        )
    ]
    value_path = consumptions[
        (
            "Q3.Plant.Transitive",
            "Q3.Plant.A",
            "ELABORATED_VALUE",
            "Q3.Plant.WValue",
        )
    ]
    assert type_path["path"] == [
        "Q3.Plant.Transitive",
        "Q3.Plant.WType",
        "Q3.Plant.A",
    ]
    assert value_path["path"] == [
        "Q3.Plant.Transitive",
        "Q3.Plant.WValue",
        "Q3.Plant.A",
    ]
    assert not any(key[1] == "Q3.Plant.B" for key in consumptions)
    assert not any(key[1] == "Q3.Plant.Definition" for key in consumptions)
    definition = next(
        row for row in snapshot["declarations"] if row["name"] == "Q3.Plant.Definition"
    )
    assert definition["value_fingerprint"] is not None


def test_snapshot_canonical_deduplicates_identical_graph_rows() -> None:
    graph = [
        graph_row("Q3.Plant.A"),
        graph_row("Q3.Plant.Consumer", value_refs=("Q3.Plant.A",)),
    ]
    metadata = [metadata_row("Q3.Plant.A"), metadata_row("Q3.Plant.Consumer")]
    expected = runtime.snapshot_from_rows(
        graph,
        metadata,
        import_modules=["Q3.Plant"],
        target_declarations=["Q3.Plant.A"],
    )
    actual = runtime.snapshot_from_rows(
        [graph[1], graph[0], dict(graph[1]), dict(graph[0])],
        metadata,
        import_modules=["Q3.Plant"],
        target_declarations=["Q3.Plant.A"],
    )
    assert actual == expected
    assert actual["consumptions"] == [
        {
            "consumer": "Q3.Plant.Consumer",
            "theorem": "Q3.Plant.A",
            "relation": "DIRECT",
            "path": ["Q3.Plant.Consumer", "Q3.Plant.A"],
            "hypothesis_port": {
                "surface": "ELABORATED_VALUE",
                "direct_reference": "Q3.Plant.A",
            },
        }
    ]


def test_snapshot_rejects_conflicting_duplicate_graph_rows() -> None:
    with pytest.raises(
        runtime.LeanDependencyError,
        match="LEAN_DEPENDENCY_GRAPH_DECLARATION_DUPLICATE_CONFLICT",
    ):
        runtime.snapshot_from_rows(
            [
                graph_row("Q3.Plant.A"),
                graph_row("Q3.Plant.A", module="Q3.Other"),
            ],
            [metadata_row("Q3.Plant.A")],
            import_modules=["Q3.Plant"],
            target_declarations=["Q3.Plant.A"],
        )


def test_snapshot_rejects_surface_drift_and_semantic_theorem() -> None:
    drift = graph_row("Q3.Plant.A", type_refs=("Q3.Plant.B",))
    drift["direct_refs"] = []
    with pytest.raises(runtime.LeanDependencyError, match="REFERENCE_SURFACE_DRIFT"):
        runtime.snapshot_from_rows(
            [drift, graph_row("Q3.Plant.B")],
            [metadata_row("Q3.Plant.A"), metadata_row("Q3.Plant.B")],
            import_modules=["Q3.Plant"],
            target_declarations=["Q3.Plant.B"],
        )

    with pytest.raises(runtime.LeanDependencyError, match="SEMANTIC_VALUE_FINGERPRINT"):
        runtime.snapshot_from_rows(
            [graph_row("Q3.Plant.A")],
            [metadata_row("Q3.Plant.A", semantic=True)],
            import_modules=["Q3.Plant"],
            target_declarations=["Q3.Plant.A"],
            semantic_declarations=["Q3.Plant.A"],
        )


def test_snapshot_fails_closed_on_unmappable_private_consumer() -> None:
    private_name = "_private.Q3.Plant.0.Helper"
    graph = [
        graph_row("Q3.Plant.A"),
        graph_row(private_name, value_refs=("Q3.Plant.A",)),
    ]
    with pytest.raises(
        runtime.LeanDependencyError,
        match="LEAN_DEPENDENCY_NONCANONICAL_CONSUMER_UNMAPPABLE",
    ):
        runtime.snapshot_from_rows(
            graph,
            [metadata_row("Q3.Plant.A"), metadata_row(private_name)],
            import_modules=["Q3.Plant"],
            target_declarations=["Q3.Plant.A"],
        )


def test_snapshot_accepts_irrelevant_unicode_private_environment_declaration() -> None:
    snapshot = runtime.snapshot_from_rows(
        [graph_row("Q3.Plant.A"), graph_row(UNICODE_PRIVATE_NAME)],
        [metadata_row("Q3.Plant.A")],
        import_modules=["Q3.Plant"],
        target_declarations=["Q3.Plant.A"],
    )
    assert [row["name"] for row in snapshot["declarations"]] == ["Q3.Plant.A"]


def test_run_source_uses_stdin_and_never_a_temp_file(tmp_path: Path, monkeypatch) -> None:
    (tmp_path / "q3.lean.aristotle").mkdir()
    calls: list[tuple[list[str], dict[str, object]]] = []

    def fake_run(command, **kwargs):
        calls.append((command, kwargs))
        return subprocess.CompletedProcess(command, 0, "ok", "")

    monkeypatch.setattr(runtime.subprocess, "run", fake_run)
    output, receipt = runtime._run_source(tmp_path, "import Lean\n", timeout=3)
    assert output.startswith("ok")
    assert calls[0][0] == ["lake", "env", "lean", "--stdin"]
    assert calls[0][1]["input"] == "import Lean\n"
    assert receipt["stdin_sha256"] == hashlib.sha256(b"import Lean\n").hexdigest()
    assert receipt["stdout_sha256"] == hashlib.sha256(b"ok").hexdigest()


def test_subprocess_failures_have_stable_taxonomy(tmp_path: Path, monkeypatch) -> None:
    (tmp_path / "q3.lean.aristotle").mkdir()

    def timeout(*args, **kwargs):
        raise subprocess.TimeoutExpired(args[0], kwargs["timeout"])

    monkeypatch.setattr(runtime.subprocess, "run", timeout)
    with pytest.raises(runtime.LeanDependencyError, match="PROBE_TIMEOUT"):
        runtime._run_source(tmp_path, "import Lean\n", timeout=3)
    with pytest.raises(runtime.LeanDependencyError, match="BUILD_TIMEOUT"):
        runtime._run_build(tmp_path, ["Q3.A"], timeout=3)


def test_run_build_materializes_modules_before_probe(tmp_path: Path, monkeypatch) -> None:
    (tmp_path / "q3.lean.aristotle").mkdir()
    calls: list[tuple[list[str], dict[str, object]]] = []

    def fake_run(command, **kwargs):
        calls.append((command, kwargs))
        return subprocess.CompletedProcess(command, 0, "ok", "")

    monkeypatch.setattr(runtime.subprocess, "run", fake_run)
    receipt = runtime._run_build(tmp_path, ["Q3.B", "Q3.A"], timeout=3)
    assert calls[0][0] == ["lake", "build", "Q3.A", "Q3.B"]
    assert "LD_LIBRARY_PATH" not in calls[0][1]["env"]
    assert receipt["returncode"] == 0


def test_inspection_orders_build_graph_metadata_and_binds_source_map(
    tmp_path: Path, monkeypatch
) -> None:
    lean_root = make_project(tmp_path)
    source = lean_root / "Q3/Plant.lean"
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text("theorem A : True := by trivial\n", encoding="utf-8")
    events: list[str] = []

    def fake_build(repo, modules, *, timeout):
        events.append("build")
        return action_receipt(["lake", "build", *modules])

    graph_payload = json.dumps(graph_row("Q3.Plant.A"))
    metadata_payload = json.dumps(metadata_row("Q3.Plant.A"))

    def fake_source(repo, text, *, timeout):
        if '"GRAPH"' in text:
            events.append("graph")
            return fake_graph_output(graph_payload), action_receipt(
                ["lake", "env", "lean", "--stdin"], stdin=text
            )
        events.append("metadata")
        return runtime.ROW_PREFIX + metadata_payload, action_receipt(
            ["lake", "env", "lean", "--stdin"], stdin=text
        )

    monkeypatch.setattr(runtime, "_run_build", fake_build)
    monkeypatch.setattr(runtime, "_run_source", fake_source)
    snapshot = runtime.inspect_dependencies(
        tmp_path, import_modules=["Q3.Plant"], target_declarations=["Q3.Plant.A"]
    )
    assert events == ["build", "graph", "metadata"]
    evidence = snapshot["runtime_evidence"]
    assert evidence["source_paths"] == ["q3.lean.aristotle/Q3/Plant.lean"]
    assert evidence["root_source_paths"] == ["q3.lean.aristotle/Q3/Plant.lean"]
    assert evidence["prebuild_root_source_fingerprints"] == [
        {
            "path": "q3.lean.aristotle/Q3/Plant.lean",
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        }
    ]
    assert evidence["project_source_baseline"] == {
        "root_path": runtime.PROJECT_SOURCE_ROOT,
        "file_count": 1,
        "algorithm": runtime.PROJECT_SOURCE_BASELINE_ALGORITHM,
        "tree_sha256": runtime._source_tree_sha256(
            evidence["prebuild_root_source_fingerprints"]
        ),
    }
    assert evidence["source_fingerprints"][0]["sha256"] == hashlib.sha256(
        source.read_bytes()
    ).hexdigest()
    validation = evidence["validation_evidence"]
    assert validation["modules"] == ["Q3.Plant"]
    assert validation["theorem_ids"] == ["Q3.Plant.A"]
    assert validation["actions"][0]["name"] == "build"
    assert validation["hole_scan"] == {
        "patterns": ["sorry", "admit", "exact?"],
        "status": "PASS",
        "findings": [],
    }
    assert validation["theorem_axioms"] == {"Q3.Plant.A": ["Classical.choice"]}
    assert validation["dependency_result"]["status"] == "EXACT"
    assert validation["toolchain"]["path"] == "q3.lean.aristotle/lean-toolchain"


def test_inspection_rejects_source_mutation_between_probes(tmp_path: Path, monkeypatch) -> None:
    lean_root = make_project(tmp_path)
    source = lean_root / "Q3/Plant.lean"
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text("theorem A : True := by trivial\n", encoding="utf-8")
    monkeypatch.setattr(
        runtime,
        "_run_build",
        lambda repo, modules, *, timeout: action_receipt(
            ["lake", "build", *modules]
        ),
    )
    graph_payload = json.dumps(graph_row("Q3.Plant.A"))
    metadata_payload = json.dumps(metadata_row("Q3.Plant.A"))

    def fake_source(repo, text, *, timeout):
        if '"GRAPH"' in text:
            return fake_graph_output(graph_payload), action_receipt(
                ["lake", "env", "lean", "--stdin"], stdin=text
            )
        source.write_text("theorem A : True := by\n  trivial\n", encoding="utf-8")
        return runtime.ROW_PREFIX + metadata_payload, action_receipt(
            ["lake", "env", "lean", "--stdin"], stdin=text
        )

    monkeypatch.setattr(runtime, "_run_source", fake_source)
    with pytest.raises(runtime.LeanDependencyError, match="SOURCE_MAP_MUTATED_DURING_PROBE"):
        runtime.inspect_dependencies(
            tmp_path, import_modules=["Q3.Plant"], target_declarations=["Q3.Plant.A"]
        )


def test_inspection_rejects_nonclosure_source_mutation_during_metadata(
    tmp_path: Path, monkeypatch
) -> None:
    lean_root = make_project(tmp_path)
    source = lean_root / "Q3/Plant.lean"
    unrelated = lean_root / "Q3/Unrelated.lean"
    source.write_text("theorem A : True := by trivial\n", encoding="utf-8")
    unrelated.write_text("theorem U : True := by trivial\n", encoding="utf-8")
    monkeypatch.setattr(
        runtime,
        "_run_build",
        lambda repo, modules, *, timeout: action_receipt(
            ["lake", "build", *modules]
        ),
    )
    graph_payload = json.dumps(graph_row("Q3.Plant.A"))
    metadata_payload = json.dumps(metadata_row("Q3.Plant.A"))

    def fake_source(repo, text, *, timeout):
        if '"GRAPH"' in text:
            return fake_graph_output(graph_payload), action_receipt(
                ["lake", "env", "lean", "--stdin"], stdin=text
            )
        unrelated.write_text(
            "theorem U : True := by\n  trivial\n", encoding="utf-8"
        )
        return runtime.ROW_PREFIX + metadata_payload, action_receipt(
            ["lake", "env", "lean", "--stdin"], stdin=text
        )

    monkeypatch.setattr(runtime, "_run_source", fake_source)
    with pytest.raises(
        runtime.LeanDependencyError,
        match="LEAN_DEPENDENCY_PROJECT_SOURCE_MUTATED_DURING_INSPECTION",
    ):
        runtime.inspect_dependencies(
            tmp_path,
            import_modules=["Q3.Plant"],
            target_declarations=["Q3.Plant.A"],
        )


def test_inspection_requires_graph_closure_inside_prebuild_project_baseline(
    tmp_path: Path, monkeypatch
) -> None:
    lean_root = make_project(tmp_path)
    source = lean_root / "Q3/Plant.lean"
    source.write_text("theorem A : True := by trivial\n", encoding="utf-8")
    monkeypatch.setattr(
        runtime,
        "_run_build",
        lambda repo, modules, *, timeout: action_receipt(
            ["lake", "build", *modules]
        ),
    )
    graph_payload = json.dumps(graph_row("Q3.Plant.A"))

    def fake_source(repo, text, *, timeout):
        assert '"GRAPH"' in text
        return fake_graph_output(graph_payload, module="Q3.Missing"), action_receipt(
            ["lake", "env", "lean", "--stdin"], stdin=text
        )

    monkeypatch.setattr(runtime, "_run_source", fake_source)
    with pytest.raises(
        runtime.LeanDependencyError,
        match="LEAN_DEPENDENCY_IMPORT_CLOSURE_OUTSIDE_PREBUILD_BASELINE",
    ):
        runtime.inspect_dependencies(
            tmp_path,
            import_modules=["Q3.Plant"],
            target_declarations=["Q3.Plant.A"],
        )


@pytest.mark.parametrize("mutation", ["bytes", "add", "remove", "symlink"])
def test_inspection_rejects_full_project_source_mutation_during_build(
    tmp_path: Path, monkeypatch, mutation: str
) -> None:
    lean_root = make_project(tmp_path)
    root_source = lean_root / "Q3/Plant.lean"
    imported_source = lean_root / "Q3/Imported.lean"
    root_source.write_text("import Q3.Imported\n", encoding="utf-8")
    imported_source.write_text("theorem imported : True := by trivial\n", encoding="utf-8")

    def mutating_build(repo, modules, *, timeout):
        if mutation == "bytes":
            imported_source.write_text(
                "theorem imported : True := by\n  trivial\n", encoding="utf-8"
            )
        elif mutation == "add":
            (lean_root / "Q3/Added.lean").write_text(
                "theorem added : True := by trivial\n", encoding="utf-8"
            )
        elif mutation == "remove":
            imported_source.rename(lean_root / "Q3/Imported.removed")
        else:
            backup = lean_root / "Q3/Imported.backup"
            imported_source.rename(backup)
            imported_source.symlink_to(backup)
        return action_receipt(["lake", "build", *modules])

    monkeypatch.setattr(runtime, "_run_build", mutating_build)
    with pytest.raises(
        runtime.LeanDependencyError,
        match="LEAN_DEPENDENCY_PROJECT_SOURCE_MUTATED_DURING_BUILD",
    ):
        runtime.inspect_dependencies(
            tmp_path,
            import_modules=["Q3.Plant"],
            target_declarations=["Q3.Plant.A"],
        )


def test_candidate_compile_binds_exact_dirty_bytes(tmp_path: Path, monkeypatch) -> None:
    lean_root = tmp_path / "q3.lean.aristotle"
    source = lean_root / "Q3/Plant.lean"
    source.parent.mkdir(parents=True)
    source.write_text("theorem plant : True := by trivial\n", encoding="utf-8")

    def fake_run(command, **kwargs):
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(runtime.subprocess, "run", fake_run)
    receipt = runtime.validate_candidate_sources(tmp_path, ["q3.lean.aristotle/Q3/Plant.lean"])[0]
    assert receipt["command"] == ["lake", "env", "lean", "Q3/Plant.lean"]
    assert receipt["returncode"] == 0
    assert receipt["bytes_sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
    assert receipt["candidate_set"] == [
        {"path": "q3.lean.aristotle/Q3/Plant.lean", "sha256": receipt["bytes_sha256"]}
    ]


def test_candidate_multi_source_set_compiles_and_binds_every_file(
    tmp_path: Path, monkeypatch
) -> None:
    lean_root = tmp_path / "q3.lean.aristotle/Q3"
    lean_root.mkdir(parents=True)
    (lean_root / "A.lean").write_text("theorem a : True := by trivial\n", encoding="utf-8")
    (lean_root / "B.lean").write_text("theorem b : True := by trivial\n", encoding="utf-8")
    calls: list[list[str]] = []

    def fake_run(command, **kwargs):
        calls.append(command)
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(runtime.subprocess, "run", fake_run)
    receipts = runtime.validate_candidate_sources(
        tmp_path,
        ["q3.lean.aristotle/Q3/A.lean", "q3.lean.aristotle/Q3/B.lean"],
    )
    assert calls == [
        ["lake", "env", "lean", "Q3/A.lean"],
        ["lake", "env", "lean", "Q3/B.lean"],
    ]
    assert [row["path"] for row in receipts] == [
        "q3.lean.aristotle/Q3/A.lean",
        "q3.lean.aristotle/Q3/B.lean",
    ]
    assert receipts[0]["candidate_set"] == receipts[1]["candidate_set"]
    assert receipts[0]["candidate_set_sha256"] == receipts[1]["candidate_set_sha256"]


def test_candidate_detects_parent_symlink_swap(tmp_path: Path, monkeypatch) -> None:
    lean_root = tmp_path / "q3.lean.aristotle"
    source_dir = lean_root / "Q3"
    source_dir.mkdir(parents=True)
    (source_dir / "Plant.lean").write_text(
        "theorem plant : True := by trivial\n", encoding="utf-8"
    )

    def swap_parent(command, **kwargs):
        replacement = lean_root / "Q3_original"
        source_dir.rename(replacement)
        source_dir.symlink_to(replacement, target_is_directory=True)
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(runtime.subprocess, "run", swap_parent)
    with pytest.raises(runtime.LeanDependencyError, match="PATH_MUTATED_DURING_CHECK"):
        runtime.validate_candidate_sources(
            tmp_path, ["q3.lean.aristotle/Q3/Plant.lean"]
        )


def test_candidate_timeout_is_normalized(tmp_path: Path, monkeypatch) -> None:
    source = tmp_path / "q3.lean.aristotle/Q3/Plant.lean"
    source.parent.mkdir(parents=True)
    source.write_text("theorem plant : True := by trivial\n", encoding="utf-8")

    def timeout(command, **kwargs):
        raise subprocess.TimeoutExpired(command, kwargs["timeout"])

    monkeypatch.setattr(runtime.subprocess, "run", timeout)
    with pytest.raises(runtime.LeanDependencyError, match="CANDIDATE_COMPILE_TIMEOUT"):
        runtime.validate_candidate_sources(
            tmp_path, ["q3.lean.aristotle/Q3/Plant.lean"], timeout=1
        )


def test_source_evidence_rejects_traversal_and_symlink_parent(tmp_path: Path) -> None:
    real = tmp_path / "real/Q3"
    real.mkdir(parents=True)
    (real / "Plant.lean").write_text("theorem plant : True := by trivial\n", encoding="utf-8")
    (tmp_path / "q3.lean.aristotle").symlink_to(tmp_path / "real", target_is_directory=True)
    with pytest.raises(runtime.LeanDependencyError, match="SOURCE_MAP_INVALID"):
        runtime._source_evidence(
            tmp_path, ["q3.lean.aristotle/Q3/Plant.lean"]
        )
    with pytest.raises(runtime.LeanDependencyError, match="PATH_INVALID"):
        runtime._source_evidence(tmp_path, ["../real/Q3/Plant.lean"])
