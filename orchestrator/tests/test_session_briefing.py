from __future__ import annotations

import datetime as dt
import json
import tempfile
import unittest
from pathlib import Path

import yaml

from orchestrator import research_dependency_projection, roof_port_ledger, session_briefing
from scripts import q3_docs_corpus


class SessionBriefingPlants(unittest.TestCase):
    def test_checkpoint_bytes_are_deterministic_and_have_no_clock(self) -> None:
        payload = {
            "schema": session_briefing.SCHEMA,
            "head": "a" * 40,
            "route": {"goal": "058"},
            "totals": {"completed_bus_goals": 1},
        }
        first = session_briefing.checkpoint_bytes(payload)
        second = session_briefing.checkpoint_bytes(payload)
        self.assertEqual(first, second)
        self.assertNotIn(b"created_at", first)
        self.assertTrue(first.endswith(b"\n"))

    def test_delta_is_monotone_and_fails_closed_on_counter_rewrite(self) -> None:
        self.assertEqual(
            session_briefing._delta({"x": 4}, {"x": 2}),
            {"x": 2},
        )
        self.assertEqual(
            session_briefing._delta({"x": 1}, {"x": 2}),
            {"x": None},
        )

    def test_priority_age_buckets_and_signal_override(self) -> None:
        today = dt.date(2026, 8, 30)
        row = {"status": "KILLED_RECHECKABLE", "last_external_check": "2026-08-30"}
        self.assertEqual(session_briefing.debt_priority(row, today)[0], "RECENT_PASSIVE")
        row["last_external_check"] = "2026-08-20"
        self.assertEqual(session_briefing.debt_priority(row, today)[0], "NORMAL")
        row["last_external_check"] = "2026-07-01"
        self.assertEqual(session_briefing.debt_priority(row, today)[0], "HIGHLIGHT_30_PLUS")
        row["status"] = "REOPEN_CANDIDATE"
        self.assertEqual(session_briefing.debt_priority(row, today)[0], "HIGH_NEW_SIGNAL")

    def test_lifecycle_never_skips_source_verification(self) -> None:
        self.assertTrue(
            session_briefing.transition_allowed("KILLED_RECHECKABLE", "REOPEN_CANDIDATE")
        )
        self.assertFalse(
            session_briefing.transition_allowed("KILLED_RECHECKABLE", "READY_FOR_RERANK")
        )
        self.assertFalse(
            session_briefing.transition_allowed("REOPEN_CANDIDATE", "READY_FOR_RERANK")
        )
        self.assertTrue(
            session_briefing.transition_allowed("SOURCE_VERIFIED", "READY_FOR_RERANK")
        )

    def test_later_unselected_root_is_control_plane_drift(self) -> None:
        self.assertTrue(
            session_briefing.control_plane_drift(
                {
                    "dependency_root": "OLD_ROOT",
                    "latest_named_unselected_root": "NEW_ROOT",
                }
            )
        )
        self.assertFalse(
            session_briefing.control_plane_drift(
                {
                    "dependency_root": "SAME_ROOT",
                    "latest_named_unselected_root": "SAME_ROOT",
                }
            )
        )

    def test_checkpoint_loader_rejects_parallel_state_shape(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "checkpoint.json"
            path.write_text(json.dumps({"schema": "wrong", "totals": {}}) + "\n")
            with self.assertRaisesRegex(
                session_briefing.SessionBriefingError,
                "SESSION_BRIEFING_CHECKPOINT_INVALID",
            ):
                session_briefing.load_checkpoint(path)

            path.write_text(
                json.dumps(
                    {
                        "schema": session_briefing.SCHEMA,
                        "head": "a" * 40,
                        "route": {},
                        "totals": {
                            "completed_bus_goals": 1,
                            "kill_outcome_artifacts": 1,
                            "answered_requests": 1,
                            "proved_verdict_artifacts": 1,
                        },
                        "selected_dependency_root": "FORBIDDEN_PARALLEL_STATE",
                    }
                )
                + "\n"
            )
            with self.assertRaisesRegex(
                session_briefing.SessionBriefingError,
                "SESSION_BRIEFING_CHECKPOINT_INVALID",
            ):
                session_briefing.load_checkpoint(path)

    def test_briefing_and_checkpoint_are_registered_tools(self) -> None:
        manifest = yaml.safe_load(
            (session_briefing.REPO / "docs/cartographer/TOOLS.yaml").read_text(
                encoding="utf-8"
            )
        )
        tools = {
            tool["id"]: tool
            for family in manifest["tool_families"].values()
            for tool in family["tools"]
        }
        self.assertFalse(tools["routeb-session-briefing"]["writes"])
        self.assertTrue(tools["routeb-session-checkpoint"]["writes"])
        self.assertFalse(tools["research-debt-challenge"]["writes"])
        self.assertFalse(tools["roof-port-supplier-ledger"]["writes"])

    def test_battle_brief_is_the_first_session_surface(self) -> None:
        assembly = session_briefing.proof_loop.assembly_snapshot(
            session_briefing.REPO / session_briefing.ASSEMBLY_DB
        )
        totals = assembly["global"]
        roof = roof_port_ledger.build(
            session_briefing.REPO,
            session_briefing.REPO / session_briefing.ASSEMBLY_DB,
        )
        rendered = session_briefing.render_briefing(
            session_briefing.REPO,
            today=dt.date(2026, 8, 31),
        )
        self.assertTrue(rendered.startswith("Q3 PROOF LOOP — BATTLE BRIEF\n"))
        self.assertIn(
            f"  assembly bookkeeping (not proof %): fixed rows "
            f"{totals['fixed']}/{totals['total']} · READY rows {totals['proved']} · "
            f"validation {totals['validation']} · open rows {totals['open']}\n",
            rendered,
        )
        self.assertIn(
            f"  roof ports: 0/7 jointly bound · "
            f"{roof['port_summary']['candidate_supplier_terms']} candidate suppliers · "
            f"{roof['port_summary']['without_exact_supplier']} without exact supplier\n",
            rendered,
        )
        self.assertEqual(roof["semantic_slot_count"], 6)
        self.assertEqual(roof["direct_proof_input_count"], 7)
        self.assertEqual(roof["proof_percentage_interpretation"], "REJECTED")
        self.assertEqual(roof["integrity_status"], "HEAD_LOCKED")
        self.assertTrue(roof["assembly_bookkeeping"]["quarantined_edges"])
        self.assertIn(
            "  roof quarantine: 1 legacy fixed edge(s) excluded from roof closure\n",
            rendered,
        )
        self.assertIn(
            "  candidate roof ports: hH1, hanchor, hMontel, hS2\n", rendered
        )
        self.assertIn("  no exact supplier: hH2a, hS1, h510\n", rendered)
        expected_port_fields = {
            "exact_type",
            "bundled_context",
            "downstream_consumer",
            "supplier_term",
            "adapters",
            "shared_unifier",
            "source_family",
            "normalization",
            "scope",
            "verifier",
            "axioms",
            "status",
            "unused_incoming_edges",
            "missing_obligation",
        }
        self.assertEqual({row["port"] for row in roof["ports"]}, {
            "hH1", "hH2a", "hanchor", "hS1", "hMontel", "h510", "hS2"
        })
        for row in roof["ports"]:
            self.assertTrue(expected_port_fields.issubset(row))
        montel = next(row for row in roof["ports"] if row["port"] == "hMontel")
        self.assertEqual(montel["semantic_role"], "MONTEL_ASSEMBLY_BEAM_NOT_SEVENTH_SLOT")
        self.assertEqual(
            roof["closed_audit_gap"],
            "EXACT_ROOF_PORT_TO_SUPPLIER_LEDGER_AT_CURRENT_HEAD",
        )
        self.assertIn("  loop: contract → suppliers → preflight → bridge → Lean → close → recompute\n", rendered)

    def test_registry_distinguishes_research_debt_from_dead(self) -> None:
        registry = session_briefing.validate_registry(session_briefing.REPO)
        self.assertTrue(registry["debts"])
        for row in registry["debts"]:
            self.assertEqual(row["classification"], "RESEARCH_DEBT")
            self.assertIs(row["not_disproved"], True)
            self.assertTrue(row["novelty_requirement"])
            self.assertEqual(
                [entry["class"] for entry in row["alternative_interface_audit"]],
                list(session_briefing.ALTERNATIVE_INTERFACE_CLASSES),
            )
            numerical = row["alternative_interface_audit"][-1]
            self.assertEqual(numerical["class"], "NUMERICAL_HYPOTHESIS_ONLY")
            self.assertEqual(numerical["status"], "HYPOTHESIS_ONLY")

        goal056 = next(row for row in registry["debts"] if row["related_goal"] == "056")
        self.assertEqual(goal056["original_object_is"], "NOT_NECESSARY")
        self.assertNotIn(
            "GOAL056_ARBITRARY_COFINAL_PROJECTION_TAIL_THEOREM_SHAPE",
            {row["id"] for row in registry["adjudications"]},
        )
        for item in registry["adjudications"]:
            for ref in item["evidence_refs"]:
                self.assertEqual(
                    set(ref),
                    {"kind", "path", "commit", "git_blob", "scope", "claim"},
                )

    def test_adjudication_evidence_is_exact_git_bound(self) -> None:
        registry_path = session_briefing.REPO / session_briefing.DEBT_REGISTRY
        registry = json.loads(registry_path.read_text(encoding="utf-8"))
        registry["adjudications"][0]["evidence_refs"][0]["git_blob"] = "0" * 40
        with tempfile.TemporaryDirectory() as tmp:
            planted = Path(tmp) / "registry.json"
            planted.write_text(json.dumps(registry) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(
                session_briefing.SessionBriefingError,
                "RESEARCH_DEPENDENCY_REF_BLOB_DRIFT",
            ):
                session_briefing.validate_registry(session_briefing.REPO, planted)

    def test_goal058_dead_claims_are_pinned_or_downgraded(self) -> None:
        registry = session_briefing.validate_registry(session_briefing.REPO)
        adjudications = {row["id"]: row for row in registry["adjudications"]}
        pstar = adjudications["PSTAR_EQUALS_SCALAR_TIMES_SOURCE_LAGRANGE_POLYNOMIAL"]
        self.assertEqual(pstar["classification"], "MATHEMATICALLY_DEAD")
        self.assertEqual(pstar["evidence_refs"][0]["kind"], "COUNTEREXAMPLE")
        self.assertNotIn("EXACT_GROUND_EQUALS_TRIAL", adjudications)

        goal = (
            session_briefing.REPO
            / "docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md"
        ).read_text(encoding="utf-8")
        ground_block = goal.split(
            "original_requested_object: EXACT_GROUND_EQUALS_TRIAL", 1
        )[1].split("- original_requested_object:", 1)[0]
        self.assertIn("failure_type: NO_DERIVATION", ground_block)
        self.assertIn("epistemic_status: RESEARCH_DEBT", ground_block)
        self.assertIn("death_evidence: []", ground_block)

    def test_canonical_projection_is_deterministic_and_semantic(self) -> None:
        output = session_briefing.REPO / research_dependency_projection.OUTPUT
        rendered = research_dependency_projection.render(session_briefing.REPO)
        self.assertEqual(output.read_bytes(), rendered)
        self.assertTrue(rendered.endswith(b"\n"))
        self.assertIn("Mathematically dead — non-actionable".encode("utf-8"), rendered)
        selected = {
            path.relative_to(session_briefing.REPO).as_posix()
            for path in q3_docs_corpus.collect_sources(session_briefing.REPO)
        }
        self.assertIn(research_dependency_projection.OUTPUT.as_posix(), selected)

    def test_rank_prefers_even_high_unlock_unknown_over_satz9_high(self) -> None:
        registry = session_briefing.validate_registry(session_briefing.REPO)
        ranked = session_briefing.ranked_debts(
            registry["debts"], dt.date(2026, 8, 30)
        )
        self.assertEqual(
            ranked[0]["id"],
            "SELECTED_FERRERS_EVEN_SECTOR_FLOOR_CURRENT_SOURCE_SHELF",
        )


if __name__ == "__main__":
    unittest.main()
