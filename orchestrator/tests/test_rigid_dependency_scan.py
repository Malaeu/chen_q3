from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from orchestrator import research_dependency_gate, rigid_dependency_scan
from scripts import q3_docs_corpus


JUSTIFICATION = """
DOWNSTREAM_CONSUMER: Y
ACTUAL_CONSUMER_REQUIREMENT: C
ORIGINAL_OBJECT_IS: UNKNOWN
KNOWN_WEAKER_INTERFACES: [Z]
WEAKER_INTERFACE_PROBE: test Z
CONSUMER_IMPLICATION: Z => C => Y
"""


class ContextualRigidDependencyPlants(unittest.TestCase):
    def test_unjustified_blocked_theorem_fails(self) -> None:
        text = "# Current\nSTATUS: OPEN\nBLOCKED: theorem X\n"
        found = rigid_dependency_scan.scan_text("current.md", text)
        self.assertEqual(len(found), 1)
        self.assertIn("consumer", found[0].missing)

    def test_consumer_justified_block_passes(self) -> None:
        text = "# Current\nSTATUS: OPEN\nBLOCKED: theorem X\n" + JUSTIFICATION
        self.assertEqual(rigid_dependency_scan.scan_text("current.md", text), [])

    def test_evidence_in_another_section_cannot_justify_assertion(self) -> None:
        text = "# Dependency\nBLOCKED: theorem X\n# Unrelated\n" + JUSTIFICATION
        found = rigid_dependency_scan.scan_text("current.md", text)
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0].section, "Dependency")

    def test_narrow_explicit_exemption_passes(self) -> None:
        text = (
            "# Transport\nRIGID_DEPENDENCY_EXEMPTION: BYTE_IDENTITY_OR_TRUST_BINDING\n"
            "The exact source is required for byte comparison.\n"
        )
        self.assertEqual(rigid_dependency_scan.scan_text("control.md", text), [])

    def test_unknown_exemption_does_not_pass(self) -> None:
        text = (
            "# Dependency\nRIGID_DEPENDENCY_EXEMPTION: BECAUSE_WE_SAID_SO\n"
            "BLOCKED: theorem X\n"
        )
        self.assertTrue(rigid_dependency_scan.scan_text("control.md", text))

    def test_generator_fixture_fails_and_passes(self) -> None:
        bad = "def render():\n    return 'BLOCKED: theorem X'\n"
        good = "def render():\n    return '''BLOCKED: theorem X\n" + JUSTIFICATION + "'''\n"
        self.assertTrue(rigid_dependency_scan.scan_text("gen.py", bad, kind="generator"))
        self.assertEqual(rigid_dependency_scan.scan_text("gen.py", good, kind="generator"), [])

    def test_historical_closed_is_excluded(self) -> None:
        text = "# Historical\nSTATUS: CLOSED\nBLOCKED: theorem X\n"
        self.assertEqual(rigid_dependency_scan.scan_text("old.md", text), [])

    def test_nested_closed_status_does_not_hide_live_assertion(self) -> None:
        text = (
            "# Live control\nSTATUS: ACTIVE\n\n"
            "## Current rule\nBLOCKED: theorem X\n\n"
            "## Historical example\nSTATUS: CLOSED\nBLOCKED: theorem OLD_X\n"
        )
        found = rigid_dependency_scan.scan_text("control.md", text)
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0].section, "Current rule")
        self.assertEqual(found[0].assertion, "BLOCKED:")

    def test_nested_closed_status_inside_first_5000_never_closes_document(self) -> None:
        text = (
            "# Live control\n\n"
            "## Current rule\nBLOCKED: theorem X\n\n"
            "## Historical example\nSTATUS: CLOSED\n"
        )
        self.assertTrue(rigid_dependency_scan.scan_text("control.md", text))

    def test_historical_path_is_excluded(self) -> None:
        text = "# Historical\nSTATUS: OPEN\nBLOCKED: theorem X\n"
        self.assertEqual(rigid_dependency_scan.scan_text("docs/archive/old.md", text), [])

    def test_selected_goal_comes_from_execution_state_not_all_open_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            state = repo / "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
            state.parent.mkdir(parents=True)
            state.write_text(
                json.dumps({"current": {"selected_bus_goal_path": "docs/routeB_bus/058.goal.md"}}),
                encoding="utf-8",
            )
            selected = repo / "docs/routeB_bus/058.goal.md"
            selected.parent.mkdir(parents=True)
            selected.write_text("STATUS: OPEN\n", encoding="utf-8")
            stale = repo / "docs/routeB_bus/001.goal.md"
            stale.write_text("STATUS: OPEN\n", encoding="utf-8")
            surfaces = rigid_dependency_scan.discover_surfaces(repo)
            paths = {surface.path for surface in surfaces}
            self.assertIn("docs/routeB_bus/058.goal.md", paths)
            self.assertNotIn("docs/routeB_bus/001.goal.md", paths)

    def test_current_task_only_when_pointer_active(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            pointer = repo / "docs/Codex/CURRENT.md"
            pointer.parent.mkdir(parents=True)
            task = repo / "docs/Codex/TASK.md"
            task.write_text("STATUS: OPEN\n", encoding="utf-8")
            pointer.write_text(
                "```yaml\nstatus: CLOSED\ntask_file: docs/Codex/TASK.md\n```\n",
                encoding="utf-8",
            )
            self.assertNotIn("docs/Codex/TASK.md", {s.path for s in rigid_dependency_scan.discover_surfaces(repo)})
            pointer.write_text(
                "```yaml\nstatus: ACTIVE\ntask_file: docs/Codex/TASK.md\n```\n",
                encoding="utf-8",
            )
            self.assertIn("docs/Codex/TASK.md", {s.path for s in rigid_dependency_scan.discover_surfaces(repo)})

    def test_only_open_queue_request_body_is_active(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            queue = repo / "docs/routeB_bus/PROSHKA_QUEUE.md"
            queue.parent.mkdir(parents=True)
            queue.write_text(
                "## REQ-NEW\n- `STATUS: OPEN`\n- Request: `docs/routeB_bus/new.txt`\n"
                "## REQ-OLD\n- `STATUS: ANSWERED`\n- Request: `docs/routeB_bus/old.txt`\n"
                "### Historical payload\nSTATUS: OPEN\n",
                encoding="utf-8",
            )
            (repo / "docs/routeB_bus/new.txt").write_text("BLOCKED: theorem X\n", encoding="utf-8")
            (repo / "docs/routeB_bus/old.txt").write_text("BLOCKED: theorem X\n", encoding="utf-8")
            paths = {surface.path for surface in rigid_dependency_scan.discover_surfaces(repo)}
            self.assertIn("docs/routeB_bus/new.txt", paths)
            self.assertNotIn("docs/routeB_bus/old.txt", paths)

    def test_manifest_covers_every_required_active_control_and_generator(self) -> None:
        required_controls = {
            "docs/Codex/RESEARCH_DEPENDENCY_PROTOCOL.md",
            "docs/Codex/SESSION_BRIEFING.md",
            "q3.lean.aristotle/docs/PROSHKA_ENTRYPOINT.md",
            "q3.lean.aristotle/docs/PROSHKA_POLICY.md",
        }
        required_generators = {
            "orchestrator/research_dependency_projection.py",
            "scripts/build_proshka_brief.py",
        }
        self.assertTrue(required_controls.issubset(rigid_dependency_scan.STATIC_ACTIVE))
        self.assertTrue(required_generators.issubset(rigid_dependency_scan.NAMED_GENERATORS))

    def test_each_named_surface_has_an_unjustified_assertion_plant(self) -> None:
        bad_markdown = "# Live\nSTATUS: ACTIVE\nBLOCKED: theorem X\n"
        bad_generator = "def render():\n    return 'BLOCKED: theorem X'\n"
        surfaces = [
            *(rigid_dependency_scan.Surface(path, "markdown") for path in rigid_dependency_scan.STATIC_ACTIVE),
            *(rigid_dependency_scan.Surface(path, "generator") for path in rigid_dependency_scan.NAMED_GENERATORS),
        ]
        for surface in surfaces:
            with self.subTest(surface=surface.path):
                text = bad_generator if surface.kind == "generator" else bad_markdown
                self.assertTrue(
                    rigid_dependency_scan.scan_text(
                        surface.path,
                        text,
                        kind=surface.kind,
                        explicitly_selected=True,
                    )
                )

    def test_collect_sources_excludes_stale_prefixes_by_membership(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            stale = repo / "q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/request.md"
            stale.parent.mkdir(parents=True)
            stale.write_text("stale", encoding="utf-8")
            live = repo / "docs/routeB_bus/live.md"
            live.parent.mkdir(parents=True)
            live.write_text("live", encoding="utf-8")
            selected = {path.relative_to(repo).as_posix() for path in q3_docs_corpus.collect_sources(repo)}
            self.assertIn("docs/routeB_bus/live.md", selected)
            self.assertNotIn(
                "q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/request.md",
                selected,
            )

    def test_gate_rejects_actual_leaked_corpus_member(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            leaked = repo / "q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md"
            leaked.parent.mkdir(parents=True)
            leaked.write_text("stale", encoding="utf-8")
            with mock.patch.object(q3_docs_corpus, "collect_sources", return_value=[leaked]):
                with self.assertRaisesRegex(RuntimeError, "SEMANTIC_STALE_SURFACE_SELECTED"):
                    research_dependency_gate.validate_semantic_exclusions(repo)


if __name__ == "__main__":
    unittest.main()
