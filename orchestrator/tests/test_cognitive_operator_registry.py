"""Lossless plants for the M2 and legacy control-action registry."""

from __future__ import annotations

import hashlib
import sqlite3
import subprocess
import tempfile
import unittest
from pathlib import Path

from orchestrator import kb, kb_migrate_kills, spine


class CognitiveOperatorRegistryTests(unittest.TestCase):
    @staticmethod
    def _git(repo: Path, *args: str, input_text: str | None = None) -> str:
        return subprocess.run(
            ["git", *args], cwd=repo, text=True, input=input_text,
            capture_output=True, check=True,
        ).stdout.strip()

    def _temporary_receipt_repo(
        self, root: Path
    ) -> tuple[list[tuple[str, str]], list[dict[str, object]]]:
        self._git(root, "init", "-q")
        self._git(root, "config", "user.email", "plants@example.invalid")
        self._git(root, "config", "user.name", "Q3 receipt plants")
        proshka = root / "docs" / "routeB_bus" / "proshka"
        proshka.mkdir(parents=True)
        artifact_path = (
            "docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_PLANT.md"
        )
        ratifier_path = (
            "docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_PLANT.md"
        )
        (root / artifact_path).write_text(
            "COGNITIVE_OPERATOR: CONSUMER_STRENGTH_REDUCTION\n",
            encoding="utf-8",
        )
        (root / ratifier_path).write_text(
            "CONSUMER_STRENGTH_REDUCTION -> MINIMAL_LEMMA\n",
            encoding="utf-8",
        )
        self._git(root, "add", artifact_path, ratifier_path)
        self._git(root, "commit", "-qm", "receipt plant baseline")
        artifact_blob = self._git(root, "rev-parse", f"HEAD:{artifact_path}")
        ratifier_blob = self._git(root, "rev-parse", f"HEAD:{ratifier_path}")
        occurrences = [(artifact_path, "CONSUMER_STRENGTH_REDUCTION")]
        receipts = [{
            "artifact_path": artifact_path,
            "artifact_blob": artifact_blob,
            "original_token": "CONSUMER_STRENGTH_REDUCTION",
            "relation": "RELATED_NOT_EQUIVALENT",
            "related_canonical_token": "MINIMAL_LEMMA",
            "ratifying_verdict_path": ratifier_path,
            "ratifying_verdict_blob": ratifier_blob,
        }]
        return occurrences, receipts

    def test_registry_has_exact_closed_counts(self) -> None:
        payload = kb.load_operator_registry()
        receipts = kb.load_historical_operator_receipts()
        self.assertEqual(len(payload["canonical_enum"]["operators"]), 8)
        self.assertEqual(len(payload["legacy_enum"]["operators"]), 9)
        self.assertEqual(len(payload["crosswalk"]), 9)
        self.assertEqual(len(receipts["receipts"]), 5)
        self.assertFalse(receipts["live_write_allowed"])
        self.assertFalse(receipts["normalization_allowed"])
        counts = {}
        for row in payload["crosswalk"]:
            counts[row["relation"]] = counts.get(row["relation"], 0) + 1
        self.assertEqual(counts, {
            "DIRECT_ALIAS": 2,
            "RELATED_NOT_EQUIVALENT": 2,
            "LEGACY_ONLY": 5,
        })

    def test_temporary_database_materialization_and_strict_validation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            db_path = Path(tmp) / "knowledge.db"
            conn = sqlite3.connect(db_path)
            conn.execute("PRAGMA foreign_keys = ON")
            conn.executescript(kb.SCHEMA.read_text(encoding="utf-8"))
            kb.materialize_operator_registry(conn)
            conn.commit()
            self.assertEqual(conn.execute(
                "SELECT COUNT(*) FROM cognitive_operator_registry "
                "WHERE vocabulary='PROSHKA_M2'").fetchone()[0], 8)
            self.assertEqual(conn.execute(
                "SELECT COUNT(*) FROM cognitive_operator_registry "
                "WHERE vocabulary='LEGACY_CONTROL_ACTION'").fetchone()[0], 9)
            self.assertEqual(conn.execute(
                "SELECT COUNT(*) FROM cognitive_operator_crosswalk").fetchone()[0], 9)
            related = conn.execute(
                "SELECT canonical_token FROM cognitive_operator_crosswalk "
                "WHERE legacy_token='ReceiverMinimize' AND relation='RELATED_NOT_EQUIVALENT'"
            ).fetchone()
            self.assertEqual(related[0], "MINIMAL_LEMMA")
            conn.close()
            result = spine.validate_cognitive_operator_registry(
                db_path=db_path
            )
            self.assertEqual(result, {
                "schema": "q3_cognitive_operator_registry.v1",
                "canonical": 8, "legacy": 9, "crosswalk": 9,
                "historical_receipts": 5,
            })

    def test_historical_relation_set_is_exact_and_not_materialized(self) -> None:
        payload = kb.load_historical_operator_receipts()
        relations = {
            (row["original_token"], row["relation"], row["related_canonical_token"])
            for row in payload["receipts"]
        }
        self.assertEqual(relations, kb.EXPECTED_HISTORICAL_RELATIONS)
        with sqlite3.connect(f"file:{kb.DB_PATH}?mode=ro", uri=True) as conn:
            stored = {
                row[0] for row in conn.execute(
                    "SELECT token FROM cognitive_operator_registry"
                )
            }
        self.assertTrue(all(row[0] not in stored for row in relations))

    def test_swapped_related_token_is_rejected(self) -> None:
        registry = kb.load_operator_registry()
        payload = kb.load_historical_operator_receipts()
        altered = dict(payload)
        altered["receipts"] = [dict(row) for row in payload["receipts"]]
        altered["receipts"][0]["related_canonical_token"] = "UNIT_AUDIT"
        with self.assertRaisesRegex(ValueError, "relation set drift"):
            kb.validate_historical_operator_receipts_payload(altered, registry)

    def test_exact_historical_occurrences_pass_production_git_state(self) -> None:
        canonical = {
            row["token"]
            for row in kb.load_operator_registry()["canonical_enum"]["operators"]
        }
        receipts = kb.load_historical_operator_receipts()["receipts"]
        spine.validate_cognitive_operator_occurrences(
            spine._live_cognitive_operator_occurrences(), canonical, receipts
        )

    def test_source_acquisition_adjudication_fields_are_machine_bound(self) -> None:
        receipt = next(
            row for row in kb.load_historical_operator_receipts()["receipts"]
            if row["original_token"] == "SOURCE_ACQUISITION"
        )
        spine._validate_source_acquisition_adjudication(receipt)
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            target = repo / str(receipt["ratifying_verdict_path"])
            target.parent.mkdir(parents=True)
            source = spine.REPO / str(receipt["ratifying_verdict_path"])
            target.write_text(
                source.read_text(encoding="utf-8").replace(
                    "  normalization_allowed: false\n",
                    "  normalization_allowed: true\n",
                    1,
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "receipt mismatch"):
                spine._validate_source_acquisition_adjudication(receipt, repo=repo)

    def test_new_path_and_unconsumed_receipt_fail(self) -> None:
        receipt = kb.load_historical_operator_receipts()["receipts"][0]
        with self.assertRaisesRegex(ValueError, "unreceipted"):
            spine.validate_cognitive_operator_occurrences(
                [("docs/routeB_bus/proshka/COPIED.md", receipt["original_token"])],
                set(),
                [receipt],
            )
        with self.assertRaisesRegex(ValueError, "unconsumed"):
            spine.validate_cognitive_operator_occurrences([], set(), [receipt])

    def test_path_traversal_and_absolute_path_fail(self) -> None:
        for path in ("../verdict.md", "/tmp/verdict.md", "docs/routeB_bus/proshka/bad\\name.md", "docs/routeB_bus/proshka/bad\nname.md"):
            with self.subTest(path=path), self.assertRaisesRegex(
                ValueError, "noncanonical Proshka receipt path"
            ):
                spine._verify_pinned_git_file(path, "0" * 40)

    def test_worktree_blob_and_symlink_plants(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            occurrences, receipts = self._temporary_receipt_repo(repo)
            spine.validate_cognitive_operator_occurrences(
                occurrences, set(), receipts, repo=repo
            )
            artifact = repo / str(receipts[0]["artifact_path"])
            artifact.chmod(0o664)
            spine.validate_cognitive_operator_occurrences(
                occurrences, set(), receipts, repo=repo
            )
            artifact.write_text("changed\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "worktree blob drift"):
                spine.validate_cognitive_operator_occurrences(
                    occurrences, set(), receipts, repo=repo
                )
            artifact.unlink()
            artifact.symlink_to(repo / str(receipts[0]["ratifying_verdict_path"]))
            with self.assertRaisesRegex(ValueError, "non-symlink"):
                spine.validate_cognitive_operator_occurrences(
                    occurrences, set(), receipts, repo=repo
                )

    def test_staged_replacement_and_conflict_stage_plants(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            occurrences, receipts = self._temporary_receipt_repo(repo)
            artifact_path = str(receipts[0]["artifact_path"])
            artifact = repo / artifact_path
            artifact.write_text("staged replacement\n", encoding="utf-8")
            self._git(repo, "add", artifact_path)
            with self.assertRaisesRegex(ValueError, "index mode/blob/stage drift"):
                spine.validate_cognitive_operator_occurrences(
                    occurrences, set(), receipts, repo=repo
                )

            self._git(repo, "reset", "--hard", "-q", "HEAD")
            blob = str(receipts[0]["artifact_blob"])
            self._git(repo, "update-index", "--force-remove", artifact_path)
            index_info = (
                f"100644 {blob} 1\t{artifact_path}\n"
                f"100644 {blob} 2\t{artifact_path}\n"
                f"100644 {blob} 3\t{artifact_path}\n"
            )
            self._git(repo, "update-index", "--index-info", input_text=index_info)
            with self.assertRaisesRegex(ValueError, "entry count or conflict-stage"):
                spine.validate_cognitive_operator_occurrences(
                    occurrences, set(), receipts, repo=repo
                )

    def test_symlinked_parent_directory_plant(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            occurrences, receipts = self._temporary_receipt_repo(repo)
            proshka = repo / "docs" / "routeB_bus" / "proshka"
            relocated = repo / "relocated_proshka"
            proshka.rename(relocated)
            proshka.symlink_to(relocated, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "symlinked parent"):
                spine.validate_cognitive_operator_occurrences(
                    occurrences, set(), receipts, repo=repo
                )

    def test_dual_field_failed_strategies_remain_distinct(self) -> None:
        rows, evidence = kb_migrate_kills.from_yaml()
        by_id = {row["id"]: row for row in rows}
        self.assertIn("RADIUS_DRIVEN_CERTIFICATE_CUTOFF_AND_TOOTH_ALIGNED_TRANSITIO", by_id)
        pairs = {(kill_id, kind, ref) for kill_id, kind, ref in evidence}
        self.assertIn((
            "RADIUS_DRIVEN_CERTIFICATE_CUTOFF_AND_TOOTH_ALIGNED_TRANSITIO",
            "legacy_control_action", "RepresentationShift",
        ), pairs)
        self.assertIn((
            "RADIUS_DRIVEN_CERTIFICATE_CUTOFF_AND_TOOTH_ALIGNED_TRANSITIO",
            "cognitive_operator", "MINIMAL_LEMMA",
        ), pairs)
        self.assertIn((
            "FULL_PACKET_SEARCH_WITH_MULTIPLE_INDEPENDENT_FRONTS",
            "legacy_control_action", "ReceiverMinimize",
        ), pairs)
        self.assertIn((
            "FULL_PACKET_SEARCH_WITH_MULTIPLE_INDEPENDENT_FRONTS",
            "cognitive_operator", "MINIMAL_LEMMA",
        ), pairs)

    def test_unknown_live_operator_fails_closed(self) -> None:
        with self.assertRaises(spine.ControlViolation) as caught:
            spine.validate_cognitive_operator_tokens(
                ["MINIMAL_LEMMA", "NOT_A_REAL_OPERATOR"], {"MINIMAL_LEMMA"})
        self.assertEqual(
            caught.exception.code,
            "COGNITIVE_OPERATOR_REGISTRY_UNAVAILABLE_OR_INVALID",
        )

    def test_tests_do_not_mutate_production_database(self) -> None:
        before = hashlib.sha256(kb.DB_PATH.read_bytes()).hexdigest()
        kb.load_operator_registry()
        after = hashlib.sha256(kb.DB_PATH.read_bytes()).hexdigest()
        self.assertEqual(before, after)


if __name__ == "__main__":
    unittest.main()
