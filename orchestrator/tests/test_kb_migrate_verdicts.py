import unittest

from orchestrator import kb_migrate_verdicts


class VerdictIdTests(unittest.TestCase):
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
