"""Fail-closed plants for the P3 module-class registry."""

from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path

from orchestrator import module_class_registry as registry


class ModuleClassRegistryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.schema = registry.load_json(registry.SCHEMA_PATH)
        self.payload = registry.load_json(registry.REGISTRY_PATH)
        self.route_b_paths = [
            path for path in registry.tracked_lean_paths(registry.REPO)
            if path.startswith("q3.lean.aristotle/Q3/Proofs/RouteB/")
            and path.endswith(".lean")
        ]

    @staticmethod
    def exact_rule(payload: dict, rule_id: str) -> dict:
        return next(
            rule for rule in payload["rules"]["exact"] if rule["id"] == rule_id
        )

    def validate(
        self,
        payload: dict | None = None,
        schema: dict | None = None,
        *,
        tracked_paths: list[str] | None = None,
        repo: Path = registry.REPO,
        require_exists: bool = True,
    ) -> dict:
        return registry.validate_registry_payload(
            self.payload if payload is None else payload,
            self.schema if schema is None else schema,
            repo=repo,
            tracked_paths=tracked_paths,
            require_exists=require_exists,
        )

    def test_production_registry_and_live_route_b_coverage(self) -> None:
        result = self.validate()
        self.assertEqual(
            result["success"], "MODULE_CLASS_SCHEMA_AND_REGISTRY_CONTRACT_VALID"
        )
        self.assertGreater(len(self.route_b_paths), 0)
        self.assertEqual(
            result["coverage"]["all_tracked_route_b_modules"],
            len(self.route_b_paths),
        )
        self.assertEqual(result["q3_root_class"], "CONDITIONAL_COMPILED")

    def test_q3_root_exact_identity_resolves_conditional_compiled(self) -> None:
        exact = [
            registry._validate_exact_rule(
                row, f"exact[{index}]", registry.REPO, require_exists=True
            )
            for index, row in enumerate(self.payload["rules"]["exact"])
        ]
        prefix = [
            registry._validate_prefix_rule(
                row, f"prefix[{index}]", registry.REPO, require_exists=True
            )
            for index, row in enumerate(self.payload["rules"]["prefix"])
        ]
        resolved = registry.resolve_module_rule(
            {"exact": exact, "prefix": prefix}, registry.Q3_ROOT_IDENTITY
        )
        self.assertIsNotNone(resolved)
        self.assertEqual(resolved["id"], "q3_root")
        self.assertEqual(resolved["module_class"], "CONDITIONAL_COMPILED")
        self.assertEqual(resolved["lifecycle_status"], "ACTIVE")

        altered = copy.deepcopy(self.payload)
        self.exact_rule(altered, "q3_root")["module_class"] = "PUBLIC_CANONICAL"
        with self.assertRaisesRegex(
            registry.RegistryError, "Q3 root classification contract drift"
        ):
            self.validate(altered)

    def test_closed_schema_contains_all_eight_classes(self) -> None:
        classes = self.schema["$defs"]["moduleClass"]["enum"]
        self.assertEqual(tuple(classes), registry.MODULE_CLASSES)
        self.assertIn("GENERATED_VIEW", classes)
        altered = copy.deepcopy(self.schema)
        altered["$defs"]["moduleClass"]["enum"].remove("GENERATED_VIEW")
        with self.assertRaisesRegex(registry.RegistryError, "closed enum drift"):
            self.validate(schema=altered)

    def test_unknown_class_artifact_kind_lifecycle_and_trait_fail(self) -> None:
        plants = (
            (("module_class",), "LAB"),
            (("artifact_kind",), "LEAN_SOURCE"),
            (("lifecycle_status",), "CURRENT"),
            (("traits", 0), "UNREVIEWED"),
        )
        for address, value in plants:
            altered = copy.deepcopy(self.payload)
            rule = self.exact_rule(altered, "q3_root")
            if len(address) == 1:
                rule[address[0]] = value
            else:
                rule[address[0]][address[1]] = value
            with self.subTest(address=address), self.assertRaisesRegex(
                registry.RegistryError, "unknown closed-enum token"
            ):
                self.validate(altered)

    def test_unknown_keys_fail_at_every_registry_layer(self) -> None:
        targets = (
            ("root", lambda payload: payload),
            ("rules", lambda payload: payload["rules"]),
            ("exact_rule", lambda payload: self.exact_rule(payload, "q3_root")),
            ("exact_identity", lambda payload: self.exact_rule(payload, "q3_root")["identity"]),
            (
                "declaration_override",
                lambda payload: self.exact_rule(payload, "q3_basic_defs")["declaration_overrides"][0],
            ),
            (
                "override_source_identity",
                lambda payload: self.exact_rule(payload, "q3_basic_defs")["declaration_overrides"][0]["source_identity"],
            ),
            ("prefix_rule", lambda payload: payload["rules"]["prefix"][0]),
            ("prefix_match", lambda payload: payload["rules"]["prefix"][0]["match"]),
            ("coverage", lambda payload: payload["declared_coverage"][0]),
        )
        for layer, target in targets:
            altered = copy.deepcopy(self.payload)
            target(altered)["unexpected_key"] = "not machine data"
            with self.subTest(layer=layer), self.assertRaisesRegex(
                registry.RegistryError, "unknown keys"
            ):
                self.validate(altered)

    def test_schema_structural_drift_fails_closed(self) -> None:
        plants = []
        root_required = copy.deepcopy(self.schema)
        root_required["required"].remove("declared_coverage")
        plants.append(root_required)
        root_properties = copy.deepcopy(self.schema)
        root_properties["properties"]["extra"] = {"type": "string"}
        plants.append(root_properties)
        exact_required = copy.deepcopy(self.schema)
        exact_required["$defs"]["exactRule"]["required"].remove("traits")
        plants.append(exact_required)
        nested_open = copy.deepcopy(self.schema)
        nested_open["$defs"]["prefixRule"]["properties"]["match"]["additionalProperties"] = True
        plants.append(nested_open)
        definition_extra = copy.deepcopy(self.schema)
        definition_extra["$defs"]["coverageRule"]["properties"]["comment"] = {"type": "string"}
        plants.append(definition_extra)
        nested_leaf = copy.deepcopy(self.schema)
        nested_leaf["$defs"]["ruleId"]["pattern"] = ".*"
        plants.append(nested_leaf)
        discriminator = copy.deepcopy(self.schema)
        discriminator["$defs"]["exactRule"]["allOf"].pop()
        plants.append(discriminator)
        for index, altered in enumerate(plants):
            with self.subTest(index=index), self.assertRaisesRegex(
                registry.RegistryError, "contract drift"
            ):
                self.validate(schema=altered)

    def test_rule_ids_and_lean_names_are_strict_ascii(self) -> None:
        bad_ids = ("Upper", "has-dash", "кириллица", "é", "")
        for token in bad_ids:
            altered = copy.deepcopy(self.payload)
            self.exact_rule(altered, "q3_root")["id"] = token
            with self.subTest(rule_id=token), self.assertRaisesRegex(
                registry.RegistryError, r"ASCII \[a-z0-9_\]"
            ):
                self.validate(altered)
        altered_module = copy.deepcopy(self.payload)
        self.exact_rule(altered_module, "q3_root")["identity"]["lean_module"] = "QТри"
        with self.assertRaisesRegex(registry.RegistryError, "invalid ASCII Lean module"):
            self.validate(altered_module)
        altered_prefix = copy.deepcopy(self.payload)
        altered_prefix["rules"]["prefix"][0]["match"]["lean_module_prefix"] = "Q3.Proofs.RoutéB."
        with self.assertRaisesRegex(registry.RegistryError, "invalid ASCII Lean module"):
            self.validate(altered_prefix)

    def test_schema_and_python_reject_exact_rule_discriminator_plants(
        self,
    ) -> None:
        try:
            import jsonschema
        except ModuleNotFoundError:
            self.skipTest("jsonschema is not installed")

        validator = jsonschema.Draft202012Validator(self.schema)
        plants = []

        unicode_prefix = copy.deepcopy(self.payload)
        unicode_prefix["rules"]["prefix"][0]["match"][
            "lean_module_prefix"
        ] = "Q3.Proofs.RoutéB."
        plants.append((unicode_prefix, "invalid ASCII Lean module"))

        lean_with_document_identity = copy.deepcopy(self.payload)
        self.exact_rule(lean_with_document_identity, "q3_root")["identity"] = {
            "repo_relative_path": "q3.lean.aristotle/Q3.lean"
        }
        plants.append((lean_with_document_identity, "missing keys"))

        status_with_module_identity = copy.deepcopy(self.payload)
        status_rule = self.exact_rule(status_with_module_identity, "q3_root")
        status_rule["artifact_kind"] = "STATUS_DOCUMENT"
        plants.append((status_with_module_identity, "unknown keys"))

        status_with_physical_split = copy.deepcopy(self.payload)
        status_rule = self.exact_rule(status_with_physical_split, "q3_root")
        status_rule["artifact_kind"] = "STATUS_DOCUMENT"
        status_rule["identity"] = {
            "repo_relative_path": "docs/status_document_plant.md"
        }
        status_rule["physical_split"] = False
        plants.append(
            (status_with_physical_split, "document rules cannot carry module split")
        )

        status_with_override = copy.deepcopy(self.payload)
        status_rule = self.exact_rule(status_with_override, "q3_root")
        status_rule["artifact_kind"] = "STATUS_DOCUMENT"
        status_rule["identity"] = {
            "repo_relative_path": "docs/status_document_plant.md"
        }
        status_rule["declaration_overrides"] = [
            copy.deepcopy(
                self.exact_rule(status_with_override, "q3_basic_defs")[
                    "declaration_overrides"
                ][0]
            )
        ]
        plants.append(
            (status_with_override, "document rules cannot carry module split/overrides")
        )

        for index, (payload, python_error) in enumerate(plants):
            with self.subTest(index=index):
                self.assertTrue(
                    list(validator.iter_errors(payload)),
                    "JSON Schema plant unexpectedly validated",
                )
                with self.assertRaisesRegex(registry.RegistryError, python_error):
                    self.validate(payload, require_exists=False)

    def test_schema_path_pattern_boundary_defers_dot_segments_to_python(self) -> None:
        try:
            import jsonschema
        except ModuleNotFoundError:
            self.skipTest("jsonschema is not installed")

        paths = (
            "q3.lean.aristotle/../Q3.lean",
            "q3.lean.aristotle//Q3.lean",
        )
        for path in paths:
            altered = copy.deepcopy(self.payload)
            self.exact_rule(altered, "q3_root")["identity"][
                "repo_relative_path"
            ] = path
            with self.subTest(path=path):
                self.assertFalse(
                    list(
                        jsonschema.Draft202012Validator(self.schema).iter_errors(
                            altered
                        )
                    ),
                    "schema unexpectedly claims executable path canonicalization",
                )
                with self.assertRaisesRegex(
                    registry.RegistryError, "noncanonical POSIX"
                ):
                    self.validate(altered, require_exists=False)

    def test_noncanonical_paths_fail(self) -> None:
        paths = (
            "/q3.lean.aristotle/Q3/Basic/Defs.lean",
            "q3.lean.aristotle/../Q3/Basic/Defs.lean",
            "q3.lean.aristotle\\Q3\\Basic\\Defs.lean",
        )
        for path in paths:
            altered = copy.deepcopy(self.payload)
            self.exact_rule(altered, "q3_root")["identity"]["repo_relative_path"] = path
            with self.subTest(path=path), self.assertRaisesRegex(
                registry.RegistryError, "noncanonical POSIX"
            ):
                self.validate(altered, require_exists=False)

    def test_symlink_escape_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp) / "repo"
            outside = Path(temp) / "outside"
            repo.mkdir()
            outside.mkdir()
            (repo / "q3.lean.aristotle").symlink_to(outside, target_is_directory=True)
            altered = copy.deepcopy(self.payload)
            with self.assertRaisesRegex(registry.RegistryError, "symlink escape"):
                self.validate(
                    altered,
                    repo=repo,
                    tracked_paths=self.route_b_paths[:1],
                    require_exists=False,
                )

    def test_coverage_rejects_escaping_broken_and_nonfile_leaves(self) -> None:
        route_path = "q3.lean.aristotle/Q3/Proofs/RouteB/Plant.lean"
        for kind in ("escape", "broken", "directory"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as temp:
                repo = Path(temp) / "repo"
                leaf = repo / route_path
                leaf.parent.mkdir(parents=True)
                if kind == "escape":
                    outside = Path(temp) / "outside.lean"
                    outside.write_text("-- outside\n", encoding="utf-8")
                    leaf.symlink_to(outside)
                    expected = "tracked leaf symlink escape"
                elif kind == "broken":
                    leaf.symlink_to(Path(temp) / "missing.lean")
                    expected = "missing or a broken symlink"
                else:
                    leaf.mkdir()
                    expected = "not a regular file"
                with self.assertRaisesRegex(registry.RegistryError, expected):
                    self.validate(
                        repo=repo,
                        tracked_paths=[route_path],
                        require_exists=False,
                    )

    def test_duplicate_id_path_module_and_prefix_tie_fail(self) -> None:
        duplicate_id = copy.deepcopy(self.payload)
        self.exact_rule(duplicate_id, "q3_basic_defs")["id"] = "q3_root"
        with self.assertRaisesRegex(registry.RegistryError, "duplicate rule/coverage id"):
            self.validate(duplicate_id)

        duplicate_identity = copy.deepcopy(self.payload)
        clone = copy.deepcopy(self.exact_rule(duplicate_identity, "q3_root"))
        clone["id"] = "duplicate_q3_root"
        duplicate_identity["rules"]["exact"].append(clone)
        with self.assertRaisesRegex(registry.RegistryError, "duplicate exact path"):
            self.validate(duplicate_identity)

        duplicate_module = copy.deepcopy(self.payload)
        clone = copy.deepcopy(
            self.exact_rule(duplicate_module, "q3_basic_weil_square_class")
        )
        clone["id"] = "duplicate_weil_square_module"
        clone["identity"] = {
            "source_root": "alternate_source",
            "repo_relative_path": "alternate_source/Q3/Basic/WeilSquareClass.lean",
            "lean_module": "Q3.Basic.WeilSquareClass",
        }
        duplicate_module["rules"]["exact"].append(clone)
        with self.assertRaisesRegex(registry.RegistryError, "duplicate exact Lean module"):
            self.validate(duplicate_module, require_exists=False)

        prefix_tie = copy.deepcopy(self.payload)
        clone = copy.deepcopy(prefix_tie["rules"]["prefix"][0])
        clone["id"] = "route_b_modules_tie"
        prefix_tie["rules"]["prefix"].append(clone)
        with self.assertRaisesRegex(registry.RegistryError, "equal-specificity"):
            self.validate(prefix_tie)

    def test_module_path_and_prefix_path_mismatch_fail(self) -> None:
        exact = copy.deepcopy(self.payload)
        self.exact_rule(exact, "q3_root")["identity"]["lean_module"] = "Q3.Basic.NotDefs"
        with self.assertRaisesRegex(registry.RegistryError, "module/path mismatch"):
            self.validate(exact)

        prefix = copy.deepcopy(self.payload)
        prefix["rules"]["prefix"][0]["match"]["lean_module_prefix"] = "Q3.Proofs.Wrong."
        with self.assertRaisesRegex(registry.RegistryError, "module/path prefix mismatch"):
            self.validate(prefix)

    def test_exact_rule_beats_prefix_and_longest_prefix_wins(self) -> None:
        broad = copy.deepcopy(self.payload)
        broad["rules"]["prefix"].append({
            "id": "all_q3_proofs",
            "artifact_kind": "LEAN_MODULE",
            "match": {
                "source_root": "q3.lean.aristotle",
                "repo_relative_path_prefix": "q3.lean.aristotle/Q3/Proofs/",
                "lean_module_prefix": "Q3.Proofs.",
            },
            "module_class": "LEGACY",
            "lifecycle_status": "HISTORICAL",
            "traits": [],
        })
        self.validate(broad)

        exact_override = copy.deepcopy(broad)
        path = self.route_b_paths[0]
        exact_override["rules"]["exact"].append({
            "id": "bad_exact_route_b_override",
            "artifact_kind": "LEAN_MODULE",
            "identity": {
                "source_root": "q3.lean.aristotle",
                "repo_relative_path": path,
                "lean_module": registry.module_from_path("q3.lean.aristotle", path),
            },
            "module_class": "PUBLIC_CANONICAL",
            "lifecycle_status": "CANDIDATE",
            "traits": [],
        })
        with self.assertRaisesRegex(registry.RegistryError, "resolved as PUBLIC_CANONICAL"):
            self.validate(exact_override)

    def test_q3_basic_defs_override_source_is_bound(self) -> None:
        altered = copy.deepcopy(self.payload)
        override = self.exact_rule(altered, "q3_basic_defs")["declaration_overrides"][0]
        override["source_identity"] = copy.deepcopy(
            self.exact_rule(altered, "q3_basic_weil_square_class")["identity"]
        )
        with self.assertRaisesRegex(registry.RegistryError, "override source mismatch"):
            self.validate(altered)

    def test_frozen_override_removal_rename_and_fifth_member_fail(self) -> None:
        removed = copy.deepcopy(self.payload)
        self.exact_rule(removed, "q3_basic_defs")["declaration_overrides"].pop()
        renamed = copy.deepcopy(self.payload)
        self.exact_rule(renamed, "q3_basic_defs")["declaration_overrides"][0]["declaration"] = "Q3.WeilCone"
        extra = copy.deepcopy(self.payload)
        overrides = self.exact_rule(extra, "q3_basic_defs")["declaration_overrides"]
        fifth = copy.deepcopy(overrides[0])
        fifth["declaration"] = "Q3.unexpected_legacy_surface"
        overrides.append(fifth)
        for altered in (removed, renamed, extra):
            count = len(self.exact_rule(altered, "q3_basic_defs")["declaration_overrides"])
            with self.subTest(count=count), self.assertRaisesRegex(
                registry.RegistryError, "frozen Q3.Basic.Defs override set drift"
            ):
                self.validate(altered)

    def test_unclassified_tracked_route_b_module_fails(self) -> None:
        altered = copy.deepcopy(self.payload)
        altered["rules"]["prefix"] = []
        with self.assertRaisesRegex(registry.RegistryError, "unclassified tracked module"):
            self.validate(altered, tracked_paths=self.route_b_paths[:1])

    def test_duplicate_json_keys_fail_before_semantic_validation(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "duplicate.json"
            path.write_text('{"schema":"a","schema":"b"}', encoding="utf-8")
            with self.assertRaisesRegex(registry.RegistryError, "duplicate JSON key"):
                registry.load_json(path)


if __name__ == "__main__":
    unittest.main()
