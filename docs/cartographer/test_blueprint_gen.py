#!/usr/bin/env python3
"""Fail-closed plants for the generated Route-B publication blueprint."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

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
            for path in (bp.PREVIEW_PATH, bp.SRC / "content.tex"):
                self.assertIn(b"PX_RH_CLAIM: NOT_MADE", first[path])
            self.assertEqual(
                json.loads(first[bp.MANIFEST_PATH])["PX_RH_CLAIM"],
                "NOT_MADE",
            )

    def test_live_model_preserves_all_open_rows(self) -> None:
        if not bp.ENV_PATH.is_file():
            self.skipTest("live env index is not available")
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
