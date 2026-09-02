#!/usr/bin/env python3
"""Deterministic tests for EnvDump selection and atom-describer ingestion."""

from __future__ import annotations

import importlib.util
import io
import json
import subprocess
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


envdump = load_module("q3_envdump", HERE / "envdump.py")
describe = load_module("q3_atom_describe", HERE.parent / "atom_describe.py")


def record(name: str = "Q3.RouteB.sample", module: str = "Q3.Proofs.RouteB.Sample") -> dict:
    return {
        "name": name,
        "kind": "theorem",
        "type": "∀ (x : Nat), x = x",
        "levelParams": [],
        "numBinders": 1,
        "file": module,
        "line": "12",
        "doc": "sample",
        "typeConsts": ["Nat"],
        "axioms": ["propext"],
        "isPrivate": False,
        "isUnsafe": False,
    }


class EnvDumpSelectionTests(unittest.TestCase):
    def test_template_streams_environment_without_materializing_full_list(self) -> None:
        source = (HERE / "EnvDump.lean").read_text(encoding="utf-8")
        self.assertIn("in env.constants do", source)
        self.assertNotIn("env.constants.toList", source)
        self.assertIn("requested exact names missing", source)

    def test_exact_imported_name_is_not_filtered_by_import_root_module(self) -> None:
        source = (HERE / "EnvDump.lean").read_text(encoding="utf-8")
        exact_body = source.split("def dumpExact", 1)[1].split(
            "def dumpStreaming", 1
        )[0]
        self.assertIn("env.find? nm", exact_body)
        self.assertNotIn("env.constants", exact_body)
        self.assertNotIn("modules.contains", exact_body)
        self.assertIn("dumpOne env moduleName nm ci", exact_body)

    def test_orphaned_oleans_are_never_imported(self) -> None:
        selected, missing, orphaned = envdump.source_backed_modules(
            ["Q3.Proofs.RouteB.Live", "Q3.Proofs.RouteB.DeletedScratch"],
            ["Q3.Proofs.RouteB.Live", "Q3.Proofs.RouteB.NotBuilt"],
        )
        self.assertEqual(selected, ["Q3.Proofs.RouteB.Live"])
        self.assertEqual(missing, ["Q3.Proofs.RouteB.NotBuilt"])
        self.assertEqual(orphaned, ["Q3.Proofs.RouteB.DeletedScratch"])

    def test_lake_validated_selection_does_not_use_mtime_heuristic(self) -> None:
        original_built = envdump.built_modules
        original_sources = envdump.source_modules
        original_stale = envdump.stale_source_modules
        try:
            envdump.built_modules = lambda _prefix: ["Q3.Proofs.RouteB.Live"]
            envdump.source_modules = lambda _prefix: ["Q3.Proofs.RouteB.Live"]
            envdump.stale_source_modules = lambda _modules: ["Q3.Proofs.RouteB.Live"]
            selected, _sources, _never, _orphaned, stale = envdump.module_selection(
                "Q3.Proofs.RouteB", lake_validated=True
            )
        finally:
            envdump.built_modules = original_built
            envdump.source_modules = original_sources
            envdump.stale_source_modules = original_stale
        self.assertEqual(selected, ["Q3.Proofs.RouteB.Live"])
        self.assertEqual(stale, [])

    def test_expected_state_rejects_wrong_prefix_and_changed_content(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "state.json"
            path.write_text(
                json.dumps(
                    {
                        "schema": envdump.EXPECTED_STATE_SCHEMA,
                        "prefix": "Q3.Other",
                        "entries": [["source:Q3.Other", 1, "a" * 64]],
                        "dependency_digest": "b" * 64,
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "prefix/schema"):
                envdump.load_expected_state(path, "Q3.Proofs.RouteB")

    def test_content_fingerprint_binds_lake_transitive_trace(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build = root / "build"
            source = root / "Q3/Proofs/RouteB/Sample.lean"
            olean = build / "Q3/Proofs/RouteB/Sample.olean"
            trace = build / "Q3/Proofs/RouteB/Sample.trace"
            source.parent.mkdir(parents=True)
            olean.parent.mkdir(parents=True)
            source.write_text("theorem sample : True := trivial", encoding="utf-8")
            olean.write_bytes(b"olean")
            trace.write_text('{"depHash":"before"}', encoding="utf-8")
            with mock.patch.object(envdump, "LEAN_ROOT", root), mock.patch.object(
                envdump, "BUILD_LIB", build,
            ), mock.patch.object(
                envdump, "source_modules", return_value=["Q3.Proofs.RouteB.Sample"],
            ), mock.patch.object(
                envdump, "built_modules", return_value=["Q3.Proofs.RouteB.Sample"],
            ):
                before = envdump.module_content_fingerprint("Q3.Proofs.RouteB")
                trace.write_text('{"depHash":"after"}', encoding="utf-8")
                after = envdump.module_content_fingerprint("Q3.Proofs.RouteB")
        self.assertNotEqual(before, after)
        self.assertTrue(any(row[0].startswith("trace:") for row in before))

    def test_dependency_digest_changes_for_non_routeb_olean(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dependency = root / "Mathlib/Imported.olean"
            dependency.parent.mkdir(parents=True)
            dependency.write_bytes(b"before")
            with mock.patch.object(
                envdump, "dependency_artifact_roots", return_value=(("package:mathlib", root),)
            ):
                before = envdump.dependency_content_digest()
                dependency.write_bytes(b"after")
                after = envdump.dependency_content_digest()
        self.assertNotEqual(before, after)

    def test_toolchain_prefix_is_resolved_in_project_directory(self) -> None:
        completed = subprocess.CompletedProcess(
            ["lean", "--print-prefix"], 0, stdout="/toolchain\n", stderr=""
        )
        with mock.patch.object(envdump.subprocess, "run", return_value=completed) as run:
            roots = envdump.dependency_artifact_roots()
        self.assertEqual(roots[-1], ("toolchain", Path("/toolchain/lib/lean")))
        self.assertEqual(run.call_args.kwargs["cwd"], envdump.LEAN_ROOT)

    def test_dependency_digest_rejects_symlink_root_and_nested_directory(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            real = base / "real"
            real.mkdir()
            root_link = base / "root-link"
            root_link.symlink_to(real, target_is_directory=True)
            with mock.patch.object(
                envdump, "dependency_artifact_roots", return_value=(("x", root_link),)
            ):
                with self.assertRaisesRegex(ValueError, "root component"):
                    envdump.dependency_content_digest()

            nested_root = base / "nested-root"
            nested_root.mkdir()
            (nested_root / "linked-dir").symlink_to(real, target_is_directory=True)
            with mock.patch.object(
                envdump, "dependency_artifact_roots", return_value=(("x", nested_root),)
            ):
                with self.assertRaisesRegex(ValueError, "directory"):
                    envdump.dependency_content_digest()

    def test_partial_json_is_rejected(self) -> None:
        records, diagnostics = envdump._validated_records(
            json.dumps(record()) + "\n{not json}\n")
        self.assertEqual(len(records), 1)
        self.assertTrue(any("неверный JSON" in d for d in diagnostics))

    def test_truncated_elaborated_type_is_rejected(self) -> None:
        truncated = record()
        truncated["type"] = "∀ (h : True), proofConsumer ⋯"
        records, diagnostics = envdump._validated_records(
            json.dumps(truncated, ensure_ascii=False) + "\n")
        self.assertEqual(records, [])
        self.assertTrue(any("неполный pretty-print типа" in d for d in diagnostics))

    def test_failed_pretty_print_is_rejected(self) -> None:
        failed = record()
        failed["type"] = "<pp failed>"
        records, diagnostics = envdump._validated_records(
            json.dumps(failed) + "\n")
        self.assertEqual(records, [])
        self.assertTrue(any("неполный pretty-print типа" in d for d in diagnostics))

    def test_exact_name_set_mismatch_prevents_atomic_publication(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp) / "build"
            build.mkdir()
            unexpected = record(name="Q3.RouteB.unexpected")
            stderr = io.StringIO()
            with mock.patch.object(envdump, "BUILD_LIB", build), mock.patch.object(
                envdump, "module_selection",
                return_value=(["Q3.Proofs.RouteB.Sample"], [], [], [], []),
            ), mock.patch.object(
                envdump, "module_state_fingerprint", return_value=(),
            ), mock.patch.object(
                envdump, "run", return_value=(0, [unexpected], ""),
            ), mock.patch.object(
                envdump, "_write_jsonl_atomic",
            ) as publish, mock.patch.object(
                envdump.sys, "argv",
                ["envdump.py", "--name", "Q3.RouteB.requested"],
            ), redirect_stderr(stderr):
                self.assertEqual(envdump.main(), 1)
            publish.assert_not_called()
            diagnostic = stderr.getvalue()
            self.assertIn("requested exact names missing: Q3.RouteB.requested", diagnostic)
            self.assertIn("unexpected exact names returned: Q3.RouteB.unexpected", diagnostic)


class AtomDescribeEnvTests(unittest.TestCase):
    def test_non_routeb_lookup_does_not_load_env_index(self) -> None:
        source = {"file": "q3.lean.aristotle/Q3/Main.lean"}
        is_routeb = "q3.lean.aristotle/Q3/Proofs/RouteB/" in source["file"]
        self.assertFalse(is_routeb)

    def test_index_loader_rejects_duplicate_names(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "env.jsonl"
            line = json.dumps(record(), ensure_ascii=False)
            path.write_text(line + "\n" + line + "\n", encoding="utf-8")
            with self.assertRaisesRegex(describe.EnvIndexError, "дубликат"):
                describe.load_env_index(path)

    def test_index_loader_rejects_truncated_elaborated_type(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "env.jsonl"
            truncated = record()
            truncated["type"] = "proofConsumer ⋯"
            path.write_text(
                json.dumps(truncated, ensure_ascii=False) + "\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(describe.EnvIndexError, "неполный pretty-print"):
                describe.load_env_index(path)

    def test_routeb_signature_comes_from_elaborated_type(self) -> None:
        source = {
            "kind_lean": "theorem",
            "namespace": "Q3.RouteB",
            "file": "q3.lean.aristotle/Q3/Proofs/RouteB/Sample.lean",
            "line": 12,
            "signature": "theorem sample (x : Nat) : x = x",
            "docstring": "source doc",
        }
        enriched = describe.enrich_from_env(
            "sample", source, {"Q3.RouteB.sample": record()}, float("inf"))
        self.assertEqual(enriched["description_source"], "LEAN_ENV")
        self.assertEqual(enriched["elaborated_type"], "∀ (x : Nat), x = x")
        self.assertEqual(
            enriched["source_signature"], "theorem sample (x : Nat) : x = x")
        self.assertEqual(
            enriched["signature"], "Q3.RouteB.sample : ∀ (x : Nat), x = x")

    def test_qualified_projection_gets_namespace(self) -> None:
        source = {"kind_lean": "field", "namespace": "Q3.RouteB", "owner": "Family"}
        self.assertEqual(
            describe.declaration_full_name("Family.coeff", source),
            "Q3.RouteB.Family.coeff",
        )

    def test_module_identity_mismatch_fails_closed(self) -> None:
        source = {
            "kind_lean": "theorem",
            "namespace": "Q3.RouteB",
            "file": "q3.lean.aristotle/Q3/Proofs/RouteB/Sample.lean",
            "signature": "theorem sample : True",
        }
        wrong = record(module="Q3.Proofs.RouteB.Other")
        with self.assertRaisesRegex(describe.EnvIndexError, "env module"):
            describe.enrich_from_env(
                "sample", source, {"Q3.RouteB.sample": wrong}, float("inf"))


if __name__ == "__main__":
    unittest.main()
