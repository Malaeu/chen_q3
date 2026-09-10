import contextlib
import hashlib
import io
import sqlite3
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from orchestrator import kb, kb_migrate_verdicts


class VerdictIdTests(unittest.TestCase):
    def test_revised_verdict_refreshes_owned_rows_without_identity_churn(self) -> None:
        production_db = kb_migrate_verdicts.kb.DB_PATH
        production_hash = (
            hashlib.sha256(production_db.read_bytes()).digest() if production_db.exists() else None
        )
        if production_hash is not None:
            self.addCleanup(
                lambda: self.assertEqual(
                    hashlib.sha256(production_db.read_bytes()).digest(),
                    production_hash,
                )
            )
        with TemporaryDirectory() as td:
            repo = Path(td)
            folder = repo / "docs" / "routeB_bus" / "proshka"
            folder.mkdir(parents=True)
            verdict = folder / "PROSHKA_VERDICT_REVISION_2026-09-10.md"
            old = (
                "PRIMARY: KILL_OLD\nCLOSES: OLD_SUPPLIER\nOPENS: OLD_DEBT\n"
                "iteration:\n  target: CONSUMER\n  failed_strategy: OWN_STRATEGY\n"
                "  next_decisive_test: OLD_TARGET\n  invariant_learned: OLD_INVARIANT\n"
                "  new_gap_name: OLD_GAP\n  cognitive_operator_used: MINIMAL_LEMMA\n"
                "  route_score: 4\n"
            )
            verdict.write_text(old, encoding="utf-8")
            mirror = repo / "historical" / "proshka" / verdict.name
            mirror.parent.mkdir(parents=True)
            mirror.write_text(old, encoding="utf-8")
            neighbor = folder / "PROSHKA_VERDICT_NEIGHBOR_2026-09-10.md"
            neighbor.write_text(
                "iteration:\n  failed_strategy: NEIGHBOR_STRATEGY\n"
                "  next_decisive_test: KEEP_NEIGHBOR\n",
                encoding="utf-8",
            )
            (folder / "PROSHKA_VERDICT_SHARED_2026-09-10.md").write_text(
                "iteration:\n  failed_strategy: SHARED_STRATEGY\n"
                "  next_decisive_test: MUST_NOT_REPLACE_YAML\n",
                encoding="utf-8",
            )
            db = repo / "knowledge.db"
            conn = sqlite3.connect(db)
            conn.executescript(kb.SCHEMA.read_text(encoding="utf-8"))
            conn.executescript(
                "CREATE TABLE IF NOT EXISTS capability(theorem TEXT,file TEXT,lens TEXT,"
                "provides TEXT,"
                "requires TEXT,strength TEXT,run_id TEXT);"
                "CREATE TABLE IF NOT EXISTS source_ledger(source_file TEXT PRIMARY KEY,"
                "expected_rows INTEGER,"
                "migrated_at TEXT,note TEXT);"
                "INSERT INTO kill(id,unit_type,subject,status,replacement,source_file) VALUES"
                "('YAML_OWNER','strategy','SHARED_STRATEGY','standing','YAML_TARGET','strategies.yaml');"
                "INSERT INTO kill_evidence VALUES('YAML_OWNER','yaml_name','SHARED_STRATEGY');"
                "INSERT INTO kill_evidence VALUES('YAML_OWNER','route_score','KEEP_YAML');"
            )
            conn.execute(
                "INSERT INTO kill(id,unit_type,subject,status,source_file,scope_negation) "
                "VALUES('MANUAL_ROW','object','KEEP_MANUAL','killed',?,'MANUAL_SCOPE')",
                (str(verdict.relative_to(repo)),),
            )
            manual_refs = [
                ("MANUAL_ROW", "verdict", str(verdict.relative_to(repo))),
                ("MANUAL_ROW", "verdict_copy", str(mirror.relative_to(repo))),
            ]
            conn.executemany("INSERT INTO kill_evidence VALUES(?,?,?)", manual_refs)
            conn.execute(
                "INSERT INTO capability VALUES(?,?,'supplier_ledger','KEEP_FOREIGN',"
                "'','declared','other_writer')",
                (verdict.name, str(verdict.relative_to(repo))),
            )
            conn.commit()
            conn.close()
            with (
                patch.object(kb_migrate_verdicts.kb, "DB_PATH", db),
                patch.object(kb_migrate_verdicts, "REPO", repo),
                patch.object(sys, "argv", ["kb_migrate_verdicts.py"]),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                self.assertEqual(kb_migrate_verdicts.kb.DB_PATH, db)
                self.assertNotEqual(db, production_db)
                snapshot = db.read_bytes()
                with patch.object(sys, "argv", ["migrate", "--dry-run"]):
                    self.assertEqual(kb_migrate_verdicts.main(), 0)
                self.assertEqual(db.read_bytes(), snapshot)
                self.assertEqual(kb_migrate_verdicts.main(), 0)
                self.assertEqual(kb_migrate_verdicts.main(), 0)
                conn = sqlite3.connect(db)
                kid = conn.execute("SELECT id FROM kill WHERE subject='OWN_STRATEGY'").fetchone()[0]
                conn.execute(
                    "UPDATE kill SET scope_negation='CURATED_SCOPE' "
                    "WHERE status='killed' AND id!='MANUAL_ROW'"
                )
                conn.execute("INSERT INTO kill_alias VALUES(?,'MANUAL_ALIAS','manual')", (kid,))
                conn.execute(
                    "INSERT INTO kill(id,unit_type,subject,status,source_file) "
                    "VALUES('ORPHAN','route','KEEP_ORPHAN','killed','missing/PROSHKA_ORPHAN.md')"
                )
                conn.execute(
                    "INSERT INTO source_ledger VALUES('missing/PROSHKA_ORPHAN.md',1,'old',"
                    "'wave 3 verdicts')"
                )
                before = conn.execute("SELECT id,rowid FROM kill ORDER BY id").fetchall()
                conn.execute(
                    "INSERT INTO kill_evidence VALUES(?,'manual_note','KEEP_NOTE')", (kid,)
                )
                conn.execute(
                    "INSERT INTO link(from_type,from_id,to_type,to_id,relation) "
                    "VALUES('kill',?,'dossier','KEEP_LINK','cites')",
                    (kid,),
                )
                conn.commit()
                conn.close()
                revised = (
                    old.replace("OLD_", "NEW_")
                    .replace("KILL_OLD", "KILL_NEW")
                    .replace("  route_score: 4\n", "")
                )
                verdict.write_text(revised, encoding="utf-8")
                mirror.rename(mirror.with_name("retired.md"))
                neighbor.write_text(neighbor.read_text().replace("KEEP_NEIGHBOR", "NOT_SELECTED"))
                selected_args = [
                    "kb_migrate_verdicts.py",
                    "--source",
                    str(verdict.relative_to(repo)),
                ]
                with patch.object(sys, "argv", selected_args):
                    self.assertEqual(kb_migrate_verdicts.main(), 0)
                    self.assertEqual(kb_migrate_verdicts.main(), 0)
                    snapshot = db.read_bytes()
                    for removed in (
                        revised.replace("PRIMARY: KILL_NEW\n", ""), "# No components\n",
                    ):
                        verdict.write_text(removed)
                        with self.assertRaisesRegex(ValueError, "COMPONENT_CHANGE"):
                            kb_migrate_verdicts.main()
                        self.assertEqual(db.read_bytes(), snapshot)
                    verdict.write_text(revised.replace("OWN_STRATEGY", "SHARED_STRATEGY"))
                    with self.assertRaisesRegex(ValueError, "COMPONENT_CHANGE"):
                        kb_migrate_verdicts.main()
                    self.assertEqual(db.read_bytes(), snapshot)
                shared = folder / "PROSHKA_VERDICT_SHARED_2026-09-10.md"
                shared.write_text(shared.read_text().replace("SHARED_STRATEGY", "NEW_OWN"))
                with patch.object(
                    sys, "argv", ["migrate", "--source", str(shared.relative_to(repo))]
                ):
                    with self.assertRaisesRegex(ValueError, "COMPONENT_CHANGE"):
                        kb_migrate_verdicts.main()
                    self.assertEqual(db.read_bytes(), snapshot)
                with patch.object(sys, "argv", ["migrate", "--source", "not/canonical.md"]):
                    with self.assertRaisesRegex(ValueError, "SOURCE_NOT_CANONICAL"):
                        kb_migrate_verdicts.main()
                    self.assertEqual(db.read_bytes(), snapshot)
            conn = sqlite3.connect(db)
            self.assertEqual(
                conn.execute(
                    "SELECT kill_id,kind,ref FROM kill_evidence "
                    "WHERE kill_id='MANUAL_ROW' ORDER BY kind"
                ).fetchall(), manual_refs,
            )
            self.assertEqual(
                conn.execute(
                    "SELECT subject,scope_negation FROM kill WHERE id='MANUAL_ROW'"
                ).fetchone(), ("KEEP_MANUAL", "MANUAL_SCOPE"),
            )
            self.assertEqual(
                conn.execute("SELECT id,rowid FROM kill ORDER BY id").fetchall(), before
            )
            self.assertEqual(
                conn.execute(
                    "SELECT ref FROM kill_evidence WHERE kill_id=? AND kind='verdict_copy'",
                    (kid,),
                ).fetchall(),
                [(str(verdict.relative_to(repo)),)],
            )
            self.assertEqual(
                conn.execute("SELECT replacement FROM kill WHERE id=?", (kid,)).fetchone(),
                ("NEW_TARGET",),
            )
            self.assertEqual(
                conn.execute("SELECT replacement FROM kill WHERE id='YAML_OWNER'").fetchone(),
                ("YAML_TARGET",),
            )
            self.assertEqual(
                conn.execute(
                    "SELECT stop_code FROM kill WHERE scope_negation='CURATED_SCOPE'"
                ).fetchone(),
                ("KILL_NEW",),
            )
            self.assertEqual(
                conn.execute("SELECT scope_negation FROM kill WHERE id='ORPHAN'").fetchone(),
                (None,),
            )
            self.assertEqual(
                conn.execute(
                    "SELECT replacement FROM kill WHERE subject='NEIGHBOR_STRATEGY'"
                ).fetchone(),
                ("KEEP_NEIGHBOR",),
            )
            self.assertEqual(
                conn.execute(
                    "SELECT alias FROM kill_alias WHERE kill_id=? ORDER BY alias", (kid,)
                ).fetchall(),
                [("MANUAL_ALIAS",), ("NEW_GAP",)],
            )
            self.assertEqual(
                conn.execute(
                    "SELECT count(*) FROM kill_fts WHERE kill_fts MATCH 'OLD_TARGET'"
                ).fetchone(),
                (0,),
            )
            self.assertEqual(
                conn.execute(
                    "SELECT count(*) FROM kill_fts WHERE kill_fts MATCH 'NEW_TARGET'"
                ).fetchone(),
                (1,),
            )
            self.assertEqual(
                conn.execute(
                    "SELECT ref FROM kill_evidence WHERE kill_id=? AND kind='next_decisive_test'",
                    (kid,),
                ).fetchall(),
                [("NEW_TARGET",)],
            )
            self.assertEqual(
                conn.execute(
                    "SELECT ref FROM kill_evidence WHERE kill_id=? AND kind='route_score'", (kid,)
                ).fetchall(),
                [],
            )
            self.assertEqual(
                conn.execute(
                    "SELECT ref FROM kill_evidence "
                    "WHERE kill_id='YAML_OWNER' AND kind='route_score'"
                ).fetchone(),
                ("KEEP_YAML",),
            )
            self.assertEqual(
                conn.execute(
                    "SELECT ref FROM kill_evidence WHERE kill_id=? AND kind='manual_note'", (kid,)
                ).fetchone(),
                ("KEEP_NOTE",),
            )
            self.assertEqual(
                conn.execute("SELECT to_id FROM link WHERE from_id=?", (kid,)).fetchone(),
                ("KEEP_LINK",),
            )
            self.assertEqual(
                conn.execute(
                    "SELECT provides,requires FROM capability WHERE run_id='supplier_ledger_w9'"
                ).fetchall(),
                [("NEW_SUPPLIER", "NEW_DEBT")],
            )
            self.assertEqual(
                conn.execute(
                    "SELECT provides FROM capability WHERE run_id='other_writer'"
                ).fetchall(),
                [("KEEP_FOREIGN",)],
            )
            conn.close()

    def test_collect_files_excludes_machine_local_qmd_mirror(self) -> None:
        with TemporaryDirectory() as td:
            repo = Path(td)
            canonical = repo / "docs" / "routeB_bus" / "proshka"
            cached = repo / "q3.lean.aristotle" / ".qmd_cache" / "q3_docs_current"
            canonical.mkdir(parents=True)
            cached.mkdir(parents=True)
            name = "PROSHKA_VERDICT_EXAMPLE_2026-08-14.md"
            (canonical / name).write_text("PRIMARY: KILL_EXAMPLE\n", encoding="utf-8")
            (cached / name).write_text("PRIMARY: KILL_STALE\n", encoding="utf-8")

            with patch.object(kb_migrate_verdicts, "REPO", repo):
                found = kb_migrate_verdicts.collect_files()

        self.assertEqual(found[name], [canonical / name])

    def test_collect_files_excludes_machine_local_backup_prompt(self) -> None:
        with TemporaryDirectory() as td:
            repo = Path(td)
            canonical = repo / "docs" / "routeB_bus" / "proshka"
            backup = canonical / "_backups"
            canonical.mkdir(parents=True)
            backup.mkdir(parents=True)
            verdict_name = "PROSHKA_VERDICT_EXAMPLE_2026-08-15.md"
            prompt_name = "PROSHKA_SYSTEM_PROMPT_v2_working_2026-08-04_pre-arsenal.md"
            (canonical / verdict_name).write_text(
                "PRIMARY: KILL_EXAMPLE\n", encoding="utf-8"
            )
            (backup / prompt_name).write_text(
                "PRIMARY: KILL_FALSE_POSITIVE\n", encoding="utf-8"
            )

            with patch.object(kb_migrate_verdicts, "REPO", repo):
                found = kb_migrate_verdicts.collect_files()

        self.assertEqual(found, {verdict_name: [canonical / verdict_name]})

    def test_reconcile_projection_removes_cache_evidence_and_source_orphan(self) -> None:
        with TemporaryDirectory() as td:
            repo = Path(td)
            conn = sqlite3.connect(":memory:")
            conn.executescript(
                """
                CREATE TABLE kill (id TEXT PRIMARY KEY, source_file TEXT NOT NULL);
                CREATE TABLE kill_evidence (
                  kill_id TEXT, kind TEXT, ref TEXT,
                  PRIMARY KEY (kill_id, kind, ref)
                );
                CREATE TABLE kill_alias (kill_id TEXT, alias TEXT);
                CREATE TABLE link (
                  from_type TEXT, from_id TEXT, to_type TEXT, to_id TEXT
                );
                CREATE TABLE source_ledger (
                  source_file TEXT PRIMARY KEY, note TEXT
                );
                INSERT INTO kill VALUES ('ORPHAN', 'docs/PROSHKA_OLD.md');
                INSERT INTO kill_evidence VALUES (
                  'ORPHAN', 'verdict_copy',
                  'q3.lean.aristotle/.qmd_cache/q3_docs_current/docs/PROSHKA_OLD.md'
                );
                INSERT INTO source_ledger VALUES (
                  'docs/PROSHKA_OLD.md', 'wave 3 verdicts'
                );
                """
            )

            with patch.object(kb_migrate_verdicts, "REPO", repo):
                removed_evidence, removed_kills = (
                    kb_migrate_verdicts.reconcile_projection(conn, set())
                )

        self.assertEqual((removed_evidence, removed_kills), (1, 1))
        self.assertEqual(conn.execute("SELECT COUNT(*) FROM kill").fetchone()[0], 0)
        self.assertEqual(
            conn.execute("SELECT COUNT(*) FROM source_ledger").fetchone()[0], 0
        )

    def test_choose_kill_id_reuses_same_named_verdict(self) -> None:
        name = "PROSHKA_VERDICT_EXAMPLE_2026-08-06.md"
        source = f"docs/routeB_bus/proshka/{name}"
        base, reused = kb_migrate_verdicts.choose_kill_id(name, source, {})
        self.assertFalse(reused)

        repeated, reused = kb_migrate_verdicts.choose_kill_id(
            name,
            f"q3.lean.aristotle/ACTIVE/requests/example/proshka/{name}",
            {base: source},
        )
        self.assertTrue(reused)
        self.assertEqual(repeated, base)

    def test_choose_kill_id_uses_stable_hash_for_real_slug_collision(self) -> None:
        name = "PROSHKA_VERDICT_EXAMPLE_2026-08-06.md"
        source = f"docs/routeB_bus/proshka/{name}"
        base, _ = kb_migrate_verdicts.choose_kill_id(name, source, {})

        collision_id, reused = kb_migrate_verdicts.choose_kill_id(
            name,
            source,
            {base: "docs/routeB_bus/proshka/PROSHKA_SOME_OTHER_VERDICT.md"},
        )
        self.assertFalse(reused)
        self.assertTrue(collision_id.startswith(base[:51] + "__"))

        repeated, reused = kb_migrate_verdicts.choose_kill_id(
            name,
            source,
            {
                base: "docs/routeB_bus/proshka/PROSHKA_SOME_OTHER_VERDICT.md",
                collision_id: source,
            },
        )
        self.assertTrue(reused)
        self.assertEqual(repeated, collision_id)

    def test_dual_iteration_and_kill_emit_two_stable_rows(self) -> None:
        with TemporaryDirectory() as td:
            repo = Path(td)
            verdict_dir = repo / "docs" / "routeB_bus" / "proshka"
            verdict_dir.mkdir(parents=True)
            verdict = verdict_dir / "PROSHKA_VERDICT_DUAL_2026-08-30.md"
            verdict.write_text(
                "# Dual verdict\n"
                "PRIMARY: KILL_EXACT_SOURCE\n"
                "iteration:\n"
                "  target: CONSUMER_Y\n"
                "  failed_strategy: THEOREM_X_DIRECT\n"
                "  new_gap_name: WEAKER_Z\n"
                "  invariant_learned: X_IS_NOT_NECESSARY\n"
                "  forbidden_future_move: DO_NOT_RETRY_X\n"
                "  next_decisive_test: TRY_Z\n",
                encoding="utf-8",
            )
            db = repo / "knowledge.db"
            conn = sqlite3.connect(db)
            conn.executescript(kb.SCHEMA.read_text(encoding="utf-8"))
            conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS capability (
                  theorem TEXT, file TEXT, lens TEXT, provides TEXT, requires TEXT,
                  strength TEXT, run_id TEXT
                );
                CREATE TABLE IF NOT EXISTS link (
                  from_type TEXT, from_id TEXT, to_type TEXT, to_id TEXT
                );
                CREATE TABLE IF NOT EXISTS source_ledger (
                  source_file TEXT PRIMARY KEY, expected_rows INTEGER,
                  migrated_at TEXT, note TEXT
                );
                """
            )
            conn.close()

            with (
                patch.object(kb_migrate_verdicts.kb, "DB_PATH", db),
                patch.object(kb_migrate_verdicts, "REPO", repo),
                patch.object(sys, "argv", ["kb_migrate_verdicts.py"]),
            ):
                self.assertEqual(kb_migrate_verdicts.main(), 0)
                self.assertEqual(kb_migrate_verdicts.main(), 0)

            conn = sqlite3.connect(db)
            rows = conn.execute(
                "SELECT id,status,scope_negation FROM kill ORDER BY status"
            ).fetchall()
            evidence = conn.execute(
                "SELECT kill_id FROM kill_evidence WHERE kind='verdict_copy'"
            ).fetchall()
            conn.close()

        self.assertEqual(len(rows), 2)
        self.assertEqual({row[1] for row in rows}, {"standing", "killed"})
        killed = next(row for row in rows if row[1] == "killed")
        self.assertIn("does not imply MATHEMATICALLY_DEAD", killed[2])
        self.assertEqual(len({row[0] for row in evidence}), 2)
        self.assertTrue(any(row[0].endswith("__VERDICT_KILL") for row in rows))


if __name__ == "__main__":
    unittest.main()

class ClosesOpensTests(unittest.TestCase):
    def test_parse_closes_opens_maps_to_provides_requires(self) -> None:
        text = (
            "# STATUS: SOURCE_WRITTEN\n"
            "```yaml\n"
            "CLOSES: SOURCE_RAYLEIGH_PROXIMITY_TO_FIXED_SHIFT\n"
            "OPENS: none\n"
            "LEAN_PATH:\n"
            "  q3.lean.aristotle/Q3/Proofs/RouteB/Example.lean\n"
            "THEOREMS:\n"
            "  - Q3.RouteB.exampleTheorem\n"
            "```\n"
        )
        closes, opens_, lean, thm = kb_migrate_verdicts.parse_closes_opens(text)
        self.assertEqual(closes, ["SOURCE_RAYLEIGH_PROXIMITY_TO_FIXED_SHIFT"])
        self.assertEqual(opens_, [])
        self.assertEqual(lean, "q3.lean.aristotle/Q3/Proofs/RouteB/Example.lean")
        self.assertEqual(thm, "Q3.RouteB.exampleTheorem")

    def test_parse_closes_opens_absent_returns_none(self) -> None:
        self.assertIsNone(kb_migrate_verdicts.parse_closes_opens("# STATUS: OPEN\nno ledger here\n"))

    def test_parse_closes_opens_multiple_and_semicolons(self) -> None:
        text = "CLOSES: A_ONE, B_TWO\nOPENS: C_THREE; D_FOUR\n"
        closes, opens_, lean, thm = kb_migrate_verdicts.parse_closes_opens(text)
        self.assertEqual(closes, ["A_ONE", "B_TWO"])
        self.assertEqual(opens_, ["C_THREE", "D_FOUR"])

    def test_parse_closes_opens_block_list_form(self) -> None:
        text = "CLOSES: []\nOPENS:\n  - FIRST_INPUT\n  - SECOND_INPUT\n"
        closes, opens_, lean, thm = kb_migrate_verdicts.parse_closes_opens(text)
        self.assertEqual(closes, [])
        self.assertEqual(opens_, ["FIRST_INPUT", "SECOND_INPUT"])


class StrategyMemoryTests(unittest.TestCase):
    DISTANCE = 'Strategy memory: target=window-floor/T-squared mechanism; status=PROGRESS; failed_strategy=unconstrained radical distance; operator=REPRESENTATION_SHIFT; invariant=Q plus fixed physical norm on the same support; forbidden_future_move=drop denominator then infer a floor; next_test=cached correction spectral centroid. No new supplier is manufactured merely to justify another wrapper.'

    def test_explicit_distance_fields_map_to_iteration_schema(self) -> None:
        self.assertEqual(kb_migrate_verdicts.parse_iteration(self.DISTANCE), {
            "target": "window-floor/T-squared mechanism",
            "status": "PROGRESS",
            "failed_strategy": "unconstrained radical distance",
            "cognitive_operator_used": "REPRESENTATION_SHIFT",
            "invariant_learned": "Q plus fixed physical norm on the same support",
            "forbidden_future_move": "drop denominator then infer a floor",
            "next_decisive_test": "cached correction spectral centroid",
        })
        self.assertEqual(kb_migrate_verdicts.parse_verdict_kill(self.DISTANCE), (None, None))

    def test_malformed_or_unstructured_memory_is_not_imported(self) -> None:
        for text in (
            "Strategy memory: target=example; status=PROGRESS",
            self.DISTANCE.replace("operator=", "unknown="),
            self.DISTANCE.replace("operator=", "target="),
            self.DISTANCE.replace("status=PROGRESS", "status="),
            "The " + self.DISTANCE,
            self.DISTANCE + "\n" + self.DISTANCE,
        ):
            with self.subTest(text=text):
                self.assertIsNone(kb_migrate_verdicts.parse_iteration(text))
