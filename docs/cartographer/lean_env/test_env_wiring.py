#!/usr/bin/env python3
"""Deterministic tests for EnvDump selection and atom-describer ingestion."""

from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

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
    def test_orphaned_oleans_are_never_imported(self) -> None:
        selected, missing, orphaned = envdump.source_backed_modules(
            ["Q3.Proofs.RouteB.Live", "Q3.Proofs.RouteB.DeletedScratch"],
            ["Q3.Proofs.RouteB.Live", "Q3.Proofs.RouteB.NotBuilt"],
        )
        self.assertEqual(selected, ["Q3.Proofs.RouteB.Live"])
        self.assertEqual(missing, ["Q3.Proofs.RouteB.NotBuilt"])
        self.assertEqual(orphaned, ["Q3.Proofs.RouteB.DeletedScratch"])

    def test_partial_json_is_rejected(self) -> None:
        records, diagnostics = envdump._validated_records(
            json.dumps(record()) + "\n{not json}\n")
        self.assertEqual(len(records), 1)
        self.assertTrue(any("неверный JSON" in d for d in diagnostics))


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
