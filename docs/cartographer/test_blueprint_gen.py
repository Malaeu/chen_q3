#!/usr/bin/env python3
"""Fail-closed plants for the generated Route-B publication blueprint."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import blueprint_gen as bp


def assembly(
    *,
    status: str = "READY",
    supplied_by: str | None = "sample",
    supplier_file: str | None = (
        "q3.lean.aristotle/Q3/Proofs/RouteB/Sample.lean"
    ),
) -> bp.AssemblyRow:
    return bp.AssemblyRow(
        chain="CHAIN",
        step=1,
        requirement="exact target",
        required_by=None,
        supplied_by=supplied_by,
        supplier_file=supplier_file,
        supplier_line=1,
        status=status,
        note="plant",
        objects=None,
    )


def proof(
    *,
    name: str = "sample",
    status: str = "proven",
    statement: str = "theorem sample : True",
    lemma_id: str = "sample-id",
) -> bp.ProofRow:
    return bp.ProofRow(
        lemma_id=lemma_id,
        name=name,
        status=status,
        statement=statement,
        doc_path="Q3/Proofs/RouteB/Sample.lean",
    )


def env_record(
    *,
    name: str = "Q3.RouteB.Nested.sample",
    module: str = "Q3.Proofs.RouteB.Sample",
) -> dict:
    return {
        "name": name,
        "kind": "theorem",
        "type": "True",
        "levelParams": [],
        "numBinders": 0,
        "file": module,
        "line": 1,
        "doc": "",
        "typeConsts": [],
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
        "isPrivate": False,
        "isUnsafe": False,
    }


def registry_plant(root: Path) -> tuple[Path, dict, dict[str, dict]]:
    source = root / "q3.lean.aristotle/Q3/Proofs/RouteB/Supplier.lean"
    consumer = root / "q3.lean.aristotle/Q3/Proofs/RouteB/Consumer.lean"
    source.parent.mkdir(parents=True)
    source.write_text("theorem supplier : True := by trivial\n", encoding="utf-8")
    consumer.write_text("theorem consumer : True := supplier\n", encoding="utf-8")
    source_blob = bp.git_blob_digest(source.read_bytes())
    registry = {
        "schema": "q3_node_registry.v10",
        "algorithm_version": "A1",
        "mode": "PRODUCTION_V10_READ_ONLY",
        "registry_hash": "a" * 64,
        "project": {
            "roots": ["q3.lean.aristotle/Q3"],
            "root_count": 1,
            "file_count": 2,
            "project_dependency_tree_hash": "b" * 64,
        },
        "review_policy": {},
        "nodes": [{
            "node_id": "N1", "node_class": "SEMANTIC_BRIDGE",
            "lifecycle": "ADMITTED",
            "theorem_ids": ["Q3.supplier", "Q3.node_only"],
            "terminal_consumer": ["Q3.consumer", "Q3.terminal_only"],
            "source": {
                "path": source.relative_to(root).as_posix(),
                "blob": source_blob,
                "commit": "1" * 40,
            },
            "semantic_review_hash": "c" * 64,
            "validation_hash": "d" * 64,
            "semantic_review_inputs": {"exact_edges": ["E1"]},
            "validation_inputs": {"dependency_graph": {"sha256": "e" * 64}},
            "review": {"state": "ADMITTED"},
        }],
        "edges": [{
            "edge_id": "E1", "theorem": "Q3.supplier",
            "consumer": "Q3.consumer", "relation": "DIRECT",
            "path": ["Q3.consumer", "Q3.supplier"],
            "hypothesis_port": {
                "surface": "ELABORATED_VALUE",
                "direct_reference": "Q3.supplier",
            },
            "consumer_path": consumer.relative_to(root).as_posix(),
            "consumer_blob": bp.git_blob_digest(consumer.read_bytes()),
        }],
    }
    registry_path = root / "NODE_REGISTRY_V10.json"
    registry_path.write_text(json.dumps(registry), encoding="utf-8")
    env = {
        "Q3.supplier": {
            **env_record(
                name="Q3.supplier", module="Q3.Proofs.RouteB.Supplier"
            ),
            "type": "True", "axioms": [],
        },
        "Q3.consumer": {
            **env_record(
                name="Q3.consumer", module="Q3.Proofs.RouteB.Consumer"
            ),
            "type": "True", "axioms": ["propext"],
        },
        "Q3.node_only": env_record(name="Q3.node_only"),
        "Q3.terminal_only": env_record(name="Q3.terminal_only"),
        "Q3.unrelated_helper": env_record(name="Q3.unrelated_helper"),
    }
    return registry_path, registry, env


class BlueprintPlantTests(unittest.TestCase):
    def make_source(self, root: Path) -> float:
        source = root / "q3.lean.aristotle/Q3/Proofs/RouteB/Sample.lean"
        source.parent.mkdir(parents=True)
        source.write_text("theorem sample : True := by trivial\n", encoding="utf-8")
        return source.stat().st_mtime + 1

    def test_ready_prose_supplier_is_not_green(self) -> None:
        row = assembly(supplied_by="closed by report")
        nodes = bp.classify([row], [], {}, float("inf"))
        self.assertEqual(
            nodes[0].publication_status,
            "READY_WITHOUT_EXACT_DECLARATION_RECEIPT",
        )
        self.assertIsNone(nodes[0].receipt)

    def test_validation_name_never_gets_receipt(self) -> None:
        row = assembly(status="VALIDATION")
        nodes = bp.classify([row], [proof()], {}, float("inf"))
        self.assertEqual(nodes[0].publication_status, "VALIDATION_ONLY")
        self.assertIsNone(nodes[0].receipt)

    def test_gap_with_existing_declaration_stays_open(self) -> None:
        row = assembly(status="GAP")
        nodes = bp.classify([row], [proof()], {}, float("inf"))
        self.assertEqual(nodes[0].publication_status, "OPEN_MATH")
        self.assertIsNone(nodes[0].receipt)

    def test_duplicate_proof_name_fails_closed(self) -> None:
        rows = [proof(lemma_id="a"), proof(lemma_id="b")]
        with self.assertRaisesRegex(bp.BlueprintError, "duplicate"):
            bp.classify([assembly()], rows, {}, float("inf"))

    def test_non_proven_receipt_fails_closed(self) -> None:
        with self.assertRaisesRegex(bp.BlueprintError, "not proven"):
            bp.classify([assembly()], [proof(status="todo")], {}, float("inf"))

    def test_wrong_module_identity_fails_closed(self) -> None:
        env = {"Q3.RouteB.sample": env_record(module="Q3.Proofs.RouteB.Other")}
        with self.assertRaisesRegex(bp.BlueprintError, "found 0"):
            bp.classify([assembly()], [proof()], env, float("inf"))

    def test_private_or_nonstandard_axiom_receipt_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            env_mtime = self.make_source(root)
            private = env_record()
            private["isPrivate"] = True
            with self.assertRaisesRegex(bp.BlueprintError, "private"):
                bp.classify(
                    [assembly()], [proof()], {private["name"]: private},
                    env_mtime, root,
                )
            tainted = env_record()
            tainted["axioms"] = ["sorryAx"]
            with self.assertRaisesRegex(bp.BlueprintError, "nonstandard"):
                bp.classify(
                    [assembly()], [proof()], {tainted["name"]: tainted},
                    env_mtime, root,
                )

    def test_nested_namespace_resolves_exactly(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            env_mtime = self.make_source(root)
            rec = env_record()
            env = {rec["name"]: rec}
            nodes = bp.classify([assembly()], [proof()], env, env_mtime, root)
            self.assertEqual(nodes[0].publication_status, "GREEN")
            self.assertEqual(nodes[0].receipt.full_name, "Q3.RouteB.Nested.sample")

    def test_statement_round_trip_is_byte_exact(self) -> None:
        statement = (
            "theorem sample (x_y : ℕ) :\n"
            "  x_y ^ 2 = ({x_y} : Set ℕ).card \n"
        )
        block = bp.verbatim(statement)
        self.assertIn(statement, block)
        self.assertEqual(block.count(statement), 1)
        self.assertTrue(
            block.startswith("\\mbox{}\\par\\smallskip\n\\begin{Verbatim}")
        )
        self.assertTrue(block.endswith("\\end{Verbatim}\n\\smallskip\n"))

    def test_statement_cannot_end_verbatim(self) -> None:
        with self.assertRaisesRegex(bp.BlueprintError, "terminates"):
            bp.verbatim("theorem bad : True\n\\end{verbatim}")

    def test_stale_check_detects_changed_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "derived"
            path.write_bytes(b"old")
            self.assertEqual(bp.stale_paths({path: b"new"}), [path])

    def test_rendering_is_deterministic_and_keeps_honesty_token(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            env_mtime = self.make_source(root)
            rec = env_record()
            receipt = bp.resolve_receipt(
                "sample",
                "q3.lean.aristotle/Q3/Proofs/RouteB/Sample.lean",
                {"sample": [proof()]},
                {rec["name"]: rec},
                env_mtime,
                root,
            )
            self.assertIsNotNone(receipt)
            node = bp.Node(assembly(), "GREEN", receipt, "exact")
            model = bp.Model(
                nodes=(node,),
                interfaces=(receipt, receipt),
                assembly_rows_digest="a" * 64,
                proof_statement_digest="b" * 64,
                env_index_digest="c" * 64,
                generator_digest="d" * 64,
                git_head="e" * 40,
            )
            first = bp.outputs(model)
            second = bp.outputs(model)
            self.assertEqual(first, second)
            self.assertEqual(len(first), 12)
            for path in (bp.PREVIEW_PATH, bp.SRC / "content.tex"):
                self.assertIn(b"PX_RH_CLAIM: NOT_MADE", first[path])
            self.assertEqual(
                json.loads(first[bp.MANIFEST_PATH])["PX_RH_CLAIM"],
                "NOT_MADE",
            )

    def test_v2_registry_projects_only_exact_edge_declarations(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            registry_path, registry, env = registry_plant(root)
            source = root / registry["nodes"][0]["source"]["path"]
            registry_mocks = (
                mock.patch.object(
                    bp.node_registry_v10, "_project_tree_at_head",
                    return_value=([], 2, "b" * 64),
                ),
                mock.patch.object(
                    bp.node_registry_v10, "_is_ancestor", return_value=True,
                ),
                mock.patch.object(
                    bp.node_registry_v10, "_blob_at_commit",
                    return_value=registry["nodes"][0]["source"]["blob"],
                ),
            )
            with mock.patch.object(
                bp.node_registry_v10, "load_registry", return_value=registry,
            ), registry_mocks[0], registry_mocks[1], registry_mocks[2]:
                projection, declarations, axiom_map, appendix = bp.project_registry(
                    registry_path.relative_to(root), env, root
                )
            self.assertEqual({item["name"] for item in declarations}, {"Q3.supplier", "Q3.consumer"})
            declaration_by_name = {item["name"]: item for item in declarations}
            self.assertEqual(
                declaration_by_name["Q3.supplier"]["registry_anchor_path"],
                "q3.lean.aristotle/Q3/Proofs/RouteB/Supplier.lean",
            )
            self.assertEqual(
                declaration_by_name["Q3.supplier"]["actual_declaration_source_path"],
                "q3.lean.aristotle/Q3/Proofs/RouteB/Supplier.lean",
            )
            self.assertNotIn("Q3.node_only", axiom_map)
            self.assertNotIn("Q3.terminal_only", axiom_map)
            self.assertNotIn("Q3.unrelated_helper", axiom_map)
            self.assertEqual(axiom_map["Q3.consumer"], ("propext",))
            self.assertTrue(projection["edges"][0]["recorded_consumer_blob_matches_current"])
            self.assertTrue(projection["nodes"][0]["source"]["recorded_blob_matches_current"])
            self.assertTrue(projection["nodes"][0]["source"]["recorded_commit_is_ancestor"])
            self.assertEqual(appendix[0]["hypothesis_port"]["direct_reference"], "Q3.supplier")
            source.write_text("theorem supplier : False := by trivial\n", encoding="utf-8")
            with mock.patch.object(
                bp.node_registry_v10, "load_registry", return_value=registry,
            ), registry_mocks[0], registry_mocks[1], registry_mocks[2]:
                with self.assertRaisesRegex(bp.BlueprintError, "source blob drift"):
                    bp.project_registry(registry_path.relative_to(root), env, root)

    def test_registry_rejects_commit_and_project_tree_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            registry_path, registry, env = registry_plant(root)
            common = mock.patch.object(
                bp.node_registry_v10, "load_registry", return_value=registry,
            )
            with common, mock.patch.object(
                bp.node_registry_v10, "_project_tree_at_head",
                return_value=([], 3, "b" * 64),
            ):
                with self.assertRaisesRegex(bp.BlueprintError, "dependency tree drift"):
                    bp.project_registry(registry_path.relative_to(root), env, root)
            for ancestor, blob, message in (
                (False, registry["nodes"][0]["source"]["blob"], "not an ancestor"),
                (True, "f" * 40, "commit/blob drift"),
            ):
                with self.subTest(message=message), mock.patch.object(
                    bp.node_registry_v10, "load_registry", return_value=registry,
                ), mock.patch.object(
                    bp.node_registry_v10, "_project_tree_at_head",
                    return_value=([], 2, "b" * 64),
                ), mock.patch.object(
                    bp.node_registry_v10, "_is_ancestor", return_value=ancestor,
                ), mock.patch.object(
                    bp.node_registry_v10, "_blob_at_commit", return_value=blob,
                ):
                    with self.assertRaisesRegex(bp.BlueprintError, message):
                        bp.project_registry(registry_path.relative_to(root), env, root)

    def test_registry_relevant_missing_envdump_declaration_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            consumer = root / "q3.lean.aristotle/Q3/Proofs/RouteB/Consumer.lean"
            consumer.parent.mkdir(parents=True)
            consumer.write_text("theorem consumer : True := by trivial\n", encoding="utf-8")
            path = root / "registry.json"
            path.write_text(
                json.dumps({
                    "schema": "q3_node_registry.v10",
                    "nodes": [{
                        "source": {
                            "path": "q3.lean.aristotle/Q3/Proofs/RouteB/Missing.lean"
                        },
                        "theorem_ids": ["Q3.missing"],
                    }],
                    "project": {
                        "roots": ["q3.lean.aristotle/Q3"], "file_count": 1,
                        "project_dependency_tree_hash": "1" * 64,
                    },
                    "edges": [{"edge_id": "E", "theorem": "Q3.missing", "consumer": "Q3.consumer", "relation": "DIRECT", "path": ["Q3.consumer", "Q3.missing"], "hypothesis_port": {"direct_reference": "Q3.missing"}, "consumer_path": "q3.lean.aristotle/Q3/Proofs/RouteB/Consumer.lean", "consumer_blob": "0" * 40}],
                }), encoding="utf-8"
            )
            registry = json.loads(path.read_text(encoding="utf-8"))
            with mock.patch.object(
                bp.node_registry_v10, "load_registry", return_value=registry,
                ), mock.patch.object(
                bp.node_registry_v10, "_project_tree_at_head",
                return_value=([], 1, "1" * 64),
            ):
                with self.assertRaisesRegex(bp.BlueprintError, "run --prepare-env"):
                    bp.project_registry(
                        path.relative_to(root),
                        {
                            "Q3.consumer": env_record(
                                name="Q3.consumer",
                                module="Q3.Proofs.RouteB.Consumer",
                            )
                        },
                        root,
                    )

    def test_registry_strict_loader_and_blob_drift_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "registry.json"
            path.write_text("{}", encoding="utf-8")
            for code in (
                "NODE_REGISTRY_DUPLICATE_JSON_KEY",
                "NODE_REGISTRY_CANONICAL_HASH_DRIFT",
                "NODE_REGISTRY_EDGE_PATH_INVALID",
            ):
                with self.subTest(code=code), mock.patch.object(
                    bp.node_registry_v10, "load_registry",
                    side_effect=bp.node_registry_v10.NodeRegistryError(code),
                ):
                    with self.assertRaisesRegex(bp.BlueprintError, code):
                        bp.project_registry(path.relative_to(root), {}, root)

    def test_confined_repo_file_rejects_parent_absolute_and_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            outside = root.parent / "outside-blueprint-plant"
            outside.write_text("x", encoding="utf-8")
            self.addCleanup(outside.unlink)
            with self.assertRaisesRegex(bp.BlueprintError, "absolute"):
                bp.confined_repo_file(root, outside)
            with self.assertRaisesRegex(bp.BlueprintError, "non-canonical"):
                bp.confined_repo_file(root, "../outside-blueprint-plant")
            target = root / "target"
            target.write_text("x", encoding="utf-8")
            link = root / "link"
            link.symlink_to(target)
            with self.assertRaisesRegex(bp.BlueprintError, "symlink"):
                bp.confined_repo_file(root, "link")

    def test_build_model_defaults_stay_relative_and_require_fresh_env(self) -> None:
        with mock.patch.object(bp, "env_receipt_matches", return_value=False):
            with self.assertRaisesRegex(bp.BlueprintError, "--prepare-env"):
                bp.build_model()
        live_registry = bp.startup_runtime._load_unique_json(
            bp.ROOT / bp.NODE_REGISTRY_PATH
        )
        env_targets = bp.required_env_targets(live_registry, (), (), bp.ROOT)
        focused_env = {
            name: env_record(name=name, module=module)
            for name, _path, module in env_targets
        }
        route_phase = {
            "selected_goal": "docs/routeB_bus/058_sample.goal.md",
            "matching_answer": None,
            "close_receipts": {},
        }
        with mock.patch.object(
            bp, "env_receipt_matches", return_value=True,
        ), mock.patch.object(
            bp.node_registry_v10, "load_registry", return_value=live_registry,
        ), mock.patch.object(bp, "load_assembly", return_value=()), mock.patch.object(
            bp, "load_proofs", return_value=(),
        ), mock.patch.object(
            bp, "load_env", return_value=(focused_env, b"env")
        ), mock.patch.object(
            bp, "project_registry", return_value=({}, (), {}, ()),
        ) as project, mock.patch.object(
            bp, "load_route_phase", return_value=route_phase,
        ) as route, mock.patch.object(
            bp, "bibliography_digests", return_value={},
        ) as bibliography, mock.patch.object(
            bp, "classify", return_value=(),
        ), mock.patch.object(bp, "load_interfaces", return_value=()), mock.patch.object(
            bp, "tracked_input_head", return_value="a" * 40,
        ):
            bp.build_model()
        self.assertEqual(project.call_args.args[0], bp.NODE_REGISTRY_PATH)
        self.assertEqual(route.call_args.args[:2], (
            bp.EXECUTION_STATE_PATH, bp.CHANNEL_RUNTIME_PATH,
        ))
        self.assertEqual(bibliography.call_args.args[0], bp.BIBLIOGRAPHY_INPUTS)
        for path in (*route.call_args.args[:2], project.call_args.args[0]):
            self.assertFalse(path.is_absolute())

    def test_prepare_env_rejects_source_change_during_lake_validation(self) -> None:
        before = {"Q3/Proofs/RouteB/Sample.lean": "a" * 64}
        changed = {"Q3/Proofs/RouteB/Sample.lean": "b" * 64}
        completed = mock.Mock(returncode=0, stdout="", stderr="")
        with mock.patch.object(
            bp, "env_receipt_matches", return_value=False,
        ), mock.patch.object(
            bp, "routeb_env_source_fingerprint", side_effect=[before, changed],
        ), mock.patch.object(
            bp.subprocess, "run", return_value=completed,
        ) as run:
            with self.assertRaisesRegex(bp.BlueprintError, "changed during lake"):
                bp.prepare_env_index()
        run.assert_called_once()

    def test_env_receipt_is_invalidated_by_lean_template_change(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            template = root / "EnvDump.lean"
            env_index = root / "env_index.jsonl"
            receipt_path = root / "receipt.json"
            template.write_text("before", encoding="utf-8")
            env_index.write_text("{}\n", encoding="utf-8")
            build_state = (("source:Q3.Proofs.RouteB.Sample", 1, "a" * 64),)
            dependency_digest = "d" * 64
            with mock.patch.object(
                bp, "ROOT", root,
            ), mock.patch.object(
                bp, "ENV_SOURCE_INPUTS", (template,),
            ), mock.patch.object(
                bp, "routeb_source_closure", return_value=[],
            ), mock.patch.object(
                bp, "ENV_PATH", env_index,
            ), mock.patch.object(
                bp, "ENV_RECEIPT_PATH", receipt_path,
            ), mock.patch.object(
                bp.lean_envdump, "module_content_fingerprint", return_value=build_state,
            ), mock.patch.object(
                bp.lean_envdump, "dependency_content_digest", return_value=dependency_digest,
            ), mock.patch.object(
                bp.node_registry_v10, "load_registry", return_value={},
            ), mock.patch.object(
                bp, "required_env_targets",
                return_value=(("Q3.sample", "q3.lean.aristotle/Q3/Sample.lean", "Q3.Sample"),),
            ) as required_targets, mock.patch.object(
                bp, "load_assembly", return_value=(),
            ), mock.patch.object(
                bp, "load_proofs", return_value=(),
            ), mock.patch.object(
                bp,
                "load_env",
                return_value=({"Q3.sample": env_record(name="Q3.sample")}, b"env"),
            ), mock.patch.object(
                bp, "env_result_modules_sha256", return_value="e" * 64,
            ):
                inputs = bp.routeb_env_source_fingerprint()
                targets_sha256 = bp.hashlib.sha256(
                    bp.canonical_bytes(
                        {
                            "declaration_modules": (
                                (
                                    "Q3.sample",
                                    "q3.lean.aristotle/Q3/Sample.lean",
                                    "Q3.Sample",
                                ),
                            )
                        }
                    )
                ).hexdigest()
                receipt_path.write_text(
                    json.dumps(
                        {
                            "schema": "q3_routeb_env_index_receipt.v3",
                            "inputs": inputs,
                            "build_state_sha256": bp.hashlib.sha256(
                                bp.canonical_bytes(
                                    {
                                        "route_modules": build_state,
                                        "dependency_digest": dependency_digest,
                                    }
                                )
                            ).hexdigest(),
                            "targets_sha256": targets_sha256,
                            "env_index_sha256": bp.hashlib.sha256(
                                env_index.read_bytes()
                            ).hexdigest(),
                            "result_modules_sha256": "e" * 64,
                        }
                    ),
                    encoding="utf-8",
                )
                self.assertTrue(bp.env_receipt_matches())
                required_targets.return_value = (
                    *required_targets.return_value,
                    (
                        "Q3.second",
                        "q3.lean.aristotle/Q3/Second.lean",
                        "Q3.Second",
                    ),
                )
                self.assertFalse(bp.env_receipt_matches())
                required_targets.return_value = required_targets.return_value[:1]
                template.write_text("after", encoding="utf-8")
                self.assertFalse(bp.env_receipt_matches())

    def test_registry_env_targets_selects_only_edge_declaration_modules(self) -> None:
        registry = {
            "nodes": [
                {
                    "source": {"path": "q3.lean.aristotle/Q3/Proofs/RouteB/Supplier.lean"},
                    "theorem_ids": ["Q3.RouteB.supplier"],
                }
            ],
            "edges": [
                {
                    "theorem": "Q3.RouteB.supplier",
                    "consumer": "Q3.RouteB.consumer",
                    "consumer_path": "q3.lean.aristotle/Q3/Proofs/RouteB/Consumer.lean",
                    "path": ["Q3.RouteB.consumer", "Q3.RouteB.supplier"],
                    "hypothesis_port": {"direct_reference": "Q3.RouteB.supplier"},
                }
            ],
        }
        bindings = bp.registry_env_targets(registry)
        self.assertEqual(
            bindings,
            (
                (
                    "Q3.RouteB.consumer",
                    "q3.lean.aristotle/Q3/Proofs/RouteB/Consumer.lean",
                    "Q3.Proofs.RouteB.Consumer",
                ),
                (
                    "Q3.RouteB.supplier",
                    "q3.lean.aristotle/Q3/Proofs/RouteB/Supplier.lean",
                    "Q3.Proofs.RouteB.Supplier",
                ),
            ),
        )

    def test_required_env_targets_cover_live_build_model_denominator(self) -> None:
        registry = bp.startup_runtime._load_unique_json(bp.ROOT / bp.NODE_REGISTRY_PATH)
        assembly_rows = bp.load_assembly()
        proofs = bp.load_proofs()
        targets = bp.required_env_targets(registry, assembly_rows, proofs, bp.ROOT)
        names = {name for name, _path, _module in targets}
        self.assertIn("Q3.RouteB.rh_iff_centeredXi_zeros_real", names)
        self.assertIn(
            "Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots", names
        )
        by_name = bp.proof_index(proofs)
        for row in assembly_rows:
            if row.status != "READY" or not row.supplied_by or not row.supplier_file:
                continue
            short_name = row.supplied_by.strip()
            matches = tuple(by_name.get(short_name, ()))
            if len(matches) != 1:
                continue
            proof_row = matches[0]
            if (
                proof_row.status != "proven"
                or proof_row.doc_path != bp.normalize_path(row.supplier_file.strip())
            ):
                continue
            full_name, _path, _module = bp.exact_source_declaration_target(
                short_name, row.supplier_file.strip(), bp.ROOT
            )
            self.assertIn(full_name, names)

    def test_build_model_rejects_missing_required_env_before_projection(self) -> None:
        with mock.patch.object(
            bp, "env_receipt_matches", return_value=True,
        ), mock.patch.object(
            bp, "load_assembly", return_value=(),
        ), mock.patch.object(
            bp, "load_proofs", return_value=(),
        ), mock.patch.object(
            bp, "load_env", return_value=({"Q3.unrelated": env_record()}, b"env"),
        ), mock.patch.object(
            bp.node_registry_v10,
            "load_registry",
            return_value={"nodes": [], "edges": []},
        ), mock.patch.object(
            bp, "project_registry", return_value=({}, (), {}, ()),
        ) as project:
            with self.assertRaisesRegex(
                bp.BlueprintError, "lacks required build-model declarations"
            ):
                bp.build_model()
        project.assert_not_called()

    def test_registry_projection_allows_imported_theorem_in_current_closure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            registry_path, registry, env = registry_plant(root)
            env["Q3.supplier"] = {
                **env["Q3.supplier"], "file": "Q3.Proofs.RouteB.Consumer",
            }
            source_blob = registry["nodes"][0]["source"]["blob"]
            with mock.patch.object(
                bp.node_registry_v10, "load_registry", return_value=registry,
            ), mock.patch.object(
                bp.node_registry_v10, "_project_tree_at_head",
                return_value=([], 2, "b" * 64),
            ), mock.patch.object(
                bp.node_registry_v10, "_is_ancestor", return_value=True,
            ), mock.patch.object(
                bp.node_registry_v10, "_blob_at_commit", return_value=source_blob,
            ):
                _projection, declarations, _axioms, _appendix = bp.project_registry(
                    registry_path.relative_to(root), env, root
                )
            supplier = next(row for row in declarations if row["name"] == "Q3.supplier")
            self.assertEqual(
                supplier["registry_anchor_path"],
                "q3.lean.aristotle/Q3/Proofs/RouteB/Supplier.lean",
            )
            self.assertEqual(
                supplier["actual_declaration_source_path"],
                "q3.lean.aristotle/Q3/Proofs/RouteB/Consumer.lean",
            )

    def test_registry_projection_rejects_actual_module_outside_current_closure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            registry_path, registry, env = registry_plant(root)
            source_blob = registry["nodes"][0]["source"]["blob"]
            for module, message in (
                ("Q3.Proofs.RouteB.NotPresent", "outside current Route-B source closure"),
                ("Mathlib.Data.Nat.Basic", "module is invalid"),
            ):
                with self.subTest(module=module):
                    changed_env = {
                        **env,
                        "Q3.supplier": {**env["Q3.supplier"], "file": module},
                    }
                    with mock.patch.object(
                        bp.node_registry_v10, "load_registry", return_value=registry,
                    ), mock.patch.object(
                        bp.node_registry_v10, "_project_tree_at_head",
                        return_value=([], 2, "b" * 64),
                    ), mock.patch.object(
                        bp.node_registry_v10, "_is_ancestor", return_value=True,
                    ), mock.patch.object(
                        bp.node_registry_v10, "_blob_at_commit", return_value=source_blob,
                    ):
                        with self.assertRaisesRegex(bp.BlueprintError, message):
                            bp.project_registry(
                                registry_path.relative_to(root), changed_env, root
                            )

    def test_route_phase_binds_exact_goal_and_close_sidecars(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            goal = root / "docs/routeB_bus/058_sample.goal.md"
            goal.parent.mkdir(parents=True)
            goal.write_text("```yaml\nGOAL: 058\nNODE: N\nSTATUS: OPEN\n```\n", encoding="utf-8")
            execution = root / "execution.json"
            execution.write_text(json.dumps({"schema_version": "route_b_execution_state.v3_live_bus", "route_id": "R", "architecture": {"status": "ACTIVE", "route_b_rh_status": "NOT_RH"}, "operational_status": "ACTIVE", "current": {"selected_bus_goal_path": goal.relative_to(root).as_posix(), "selected_bus_goal_nnn": "058", "stage_id": "S", "contract_obligation": "C", "route_promotion": False, "rh_claimed": False}}), encoding="utf-8")
            channel = root / "channel.json"
            phase_key = {"route_id": "R", "front_id": "F", "source_object_family_id": "O", "terminal_consumer_id": "C", "honesty_state": "CHALLENGER_NOT_RH", "convention_lock_id": "L"}
            channel.write_text(json.dumps({"schema": "q3_channel_runtime.v1", "px_rh_claim_state": "NOT_READY", "active_proshka_phase": {"status": "ACTIVE", "phase_id": "P", "phase_key": phase_key}}), encoding="utf-8")
            with mock.patch.object(bp.spine, "validate_runtime", return_value={}):
                snapshot = bp.load_route_phase(execution.relative_to(root), channel.relative_to(root), root)
            self.assertEqual(snapshot["selected_goal_status"], "OPEN")
            self.assertEqual(snapshot["selected_goal_id"], "058")
            self.assertEqual(snapshot["selected_goal_node"], "N")
            self.assertEqual(snapshot["terminal_consumer"], "C")
            self.assertEqual(snapshot["honesty_state"], "CHALLENGER_NOT_RH")
            self.assertIsNone(snapshot["matching_answer"])
            self.assertEqual(snapshot["close_receipts"], {})

    def test_route_phase_rejects_invalid_or_inapplicable_close_receipts(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            goal = root / "docs/routeB_bus/058_sample.goal.md"
            goal.parent.mkdir(parents=True)
            goal.write_text("```yaml\nGOAL: 058\nNODE: N\nTERMINAL_CONSUMER: C\nSTATUS: OPEN\n```\n", encoding="utf-8")
            answer = goal.with_name("058_sample.answer.md")
            answer.write_text("```yaml\nGOAL: 058\nNODE: N\nSTATUS: CLOSED\nRESULT: exact\n```\n", encoding="utf-8")
            goal_receipt = goal.with_name("058_sample.goal-close.json")
            goal_receipt.write_text("{}\n", encoding="utf-8")
            execution = root / "execution.json"
            execution.write_text(json.dumps({"schema_version": "route_b_execution_state.v3_live_bus", "route_id": "R", "architecture": {"route_b_rh_status": "NOT_RH"}, "operational_status": "ACTIVE", "current": {"selected_bus_goal_path": goal.relative_to(root).as_posix(), "selected_bus_goal_nnn": "058", "stage_id": "S", "contract_obligation": "C", "route_promotion": False, "rh_claimed": False}}), encoding="utf-8")
            channel = root / "channel.json"
            phase_key = {"route_id": "R", "front_id": "F", "source_object_family_id": "O", "terminal_consumer_id": "C", "honesty_state": "CHALLENGER_NOT_RH", "convention_lock_id": "L"}
            channel.write_text(json.dumps({"schema": "q3_channel_runtime.v1", "px_rh_claim_state": "NOT_READY", "active_proshka_phase": {"status": "ACTIVE", "phase_id": "P", "phase_key": phase_key}}), encoding="utf-8")
            with mock.patch.object(bp.spine, "validate_runtime", return_value={}), mock.patch.object(
                bp.startup_runtime, "validate_goal_close_receipt",
                side_effect=bp.startup_runtime.StartupRuntimeError("BAD_RECEIPT"),
            ):
                with self.assertRaisesRegex(bp.BlueprintError, "goal-close receipt invalid"):
                    bp.load_route_phase(execution.relative_to(root), channel.relative_to(root), root)
            phase_receipt = goal.with_name("058_sample.phase-close.json")
            phase_receipt.write_text("{}\n", encoding="utf-8")
            with mock.patch.object(bp.spine, "validate_runtime", return_value={}), mock.patch.object(
                bp.startup_runtime, "validate_goal_close_receipt",
                return_value={"schema": "q3_goal_close_receipt.v1", "phase_close_required": False},
            ):
                with self.assertRaisesRegex(bp.BlueprintError, "not applicable"):
                    bp.load_route_phase(execution.relative_to(root), channel.relative_to(root), root)

    def test_route_phase_rejects_noncanonical_or_unbound_goal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            channel = root / "channel.json"
            phase_key = {
                "route_id": "R", "front_id": "F", "source_object_family_id": "O",
                "terminal_consumer_id": "C", "honesty_state": "CHALLENGER_NOT_RH",
                "convention_lock_id": "L",
            }
            channel.write_text(json.dumps({
                "schema": "q3_channel_runtime.v1", "px_rh_claim_state": "NOT_READY",
                "active_proshka_phase": {
                    "status": "ACTIVE", "phase_id": "P", "phase_key": phase_key,
                },
            }), encoding="utf-8")
            execution = root / "execution.json"
            for relative, header, selected_id, message in (
                ("other/058_sample.goal.md", "GOAL: 058\nNODE: N\n", "058", "outside canonical"),
                ("docs/routeB_bus/058_sample.goal.md", "GOAL: 058\nSTATUS: OPEN\n", "058", "no exact node"),
                ("docs/routeB_bus/058_sample.goal.md", "GOAL: 058\nNODE: N\nTERMINAL_CONSUMER: OTHER\nSTATUS: OPEN\n", "058", "consumer drift"),
                ("docs/routeB_bus/058_sample.goal.md", "GOAL: 058\nNODE: N\nTERMINAL_CONSUMER: C\nSTATUS: OPEN\n", "057", "identity drift"),
            ):
                with self.subTest(message=message):
                    goal = root / relative
                    goal.parent.mkdir(parents=True, exist_ok=True)
                    goal.write_text(f"```yaml\n{header}```\n", encoding="utf-8")
                    execution.write_text(json.dumps({
                        "schema_version": "route_b_execution_state.v3_live_bus",
                        "route_id": "R", "architecture": {"route_b_rh_status": "NOT_RH"},
                        "operational_status": "ACTIVE", "current": {
                            "selected_bus_goal_path": relative,
                            "selected_bus_goal_nnn": selected_id,
                            "stage_id": "S", "contract_obligation": "C",
                            "route_promotion": False, "rh_claimed": False,
                        },
                    }), encoding="utf-8")
                    with mock.patch.object(bp.spine, "validate_runtime", return_value={}):
                        with self.assertRaisesRegex(bp.BlueprintError, message):
                            bp.load_route_phase(
                                execution.relative_to(root), channel.relative_to(root), root,
                            )

    def test_live_model_preserves_all_open_rows(self) -> None:
        if not bp.ENV_PATH.is_file():
            self.skipTest("live env index is not available")
        if not bp.env_receipt_matches():
            with self.assertRaisesRegex(bp.BlueprintError, "--prepare-env"):
                bp.build_model()
            return
        model = bp.build_model()
        self.assertEqual(model.counts["assembly_rows"], 69)
        self.assertEqual(model.counts["open_math"], 18)
        self.assertEqual(model.counts["validation_only"], 3)
        for node in model.nodes:
            if node.row.status not in {"READY", "VALIDATION"}:
                self.assertEqual(node.publication_status, "OPEN_MATH")
                self.assertIsNone(node.receipt)


if __name__ == "__main__":
    unittest.main()
