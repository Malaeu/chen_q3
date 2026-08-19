import sqlite3
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from orchestrator import kb_migrate_verdicts


class VerdictIdTests(unittest.TestCase):
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
