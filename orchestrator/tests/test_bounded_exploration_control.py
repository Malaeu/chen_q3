"""P9A plants for bounded exploration and delegated authority.

Every database write in this suite targets an in-memory or temporary database.
The production knowledge.db is opened only read-only by Spine rendering.
"""

from __future__ import annotations

import hashlib
import json
import sqlite3
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from orchestrator import kb, spine


PHASE = {
    "route_id": "ROUTE_B",
    "front_id": "TEST_FRONT",
    "source_object_family_id": "SOURCE_FAMILY",
    "terminal_consumer_id": "CONSUMER",
    "honesty_state": "CHALLENGER_NOT_RH",
    "convention_lock_id": "LOCK_V1",
}


def candidate(route_id: str, theorem_shape: str) -> dict[str, object]:
    return {
        "route_id": route_id,
        "source_object": "SOURCE_OBJECT",
        "terminal_consumer": "CONSUMER",
        "normalized_theorem_shape": theorem_shape,
        "assumption_set": ["H1"],
        "conclusion": "TARGET",
        "dependency_set": ["D1"],
        "preserved_invariants": ["SOURCE_FAITHFUL"],
        "dropped_structures": [],
        "decisive_test_class": "COUNTEREXAMPLE",
        "reversible": True,
        "cheapest_killer": f"KILL_{route_id}",
    }


def valid_delta(**updates: object) -> dict[str, object]:
    delta: dict[str, object] = {
        "delta_id": "DELTA_1",
        "exploration_id": "EXP_1",
        "cycle_index": 1,
        "kind": "COUNTEREXAMPLE_FOUND",
        "scope": "ABSTRACT",
        "verifier": "PAPER",
        "subject_id": "ROUTE_A",
        "blocker_fingerprint_before": "before",
        "blocker_fingerprint_after": "after",
        "before": "two candidates",
        "after": "one candidate",
        "decision_effect": "CANDIDATE_KILLED",
        "evidence": [{"kind": "paper", "ref": "source:lemma", "sha256": "a" * 64}],
        "validated": True,
        "stall_counter_reset": True,
    }
    delta.update(updates)
    return delta


class BoundedExplorationPlants(unittest.TestCase):
    def assert_code(self, code: str, fn, *args, **kwargs) -> spine.ControlViolation:
        with self.assertRaises(spine.ControlViolation) as caught:
            fn(*args, **kwargs)
        self.assertEqual(caught.exception.code, code)
        return caught.exception

    def test_E0_valid_named_fork_enters(self) -> None:
        request = {
            "entry_gate": "NAMED_THEOREM_SHAPE_FORK",
            "candidates": [candidate("A", "SHAPE_A"), candidate("B", "SHAPE_B")],
            "same_phase_key": True,
            "same_honesty_state": True,
            "source_locked_winner_found": False,
            "already_named_single_theorem_target": False,
        }
        self.assertEqual(spine.decide_exploration_entry(request),
                         "ENTER_BOUNDED_EXPLORATION")

    def test_E1_one_hard_lemma_is_not_a_fork(self) -> None:
        request = {
            "entry_gate": "NAMED_THEOREM_SHAPE_FORK",
            "candidates": [candidate("A", "ONE_HARD_LEMMA")],
            "same_phase_key": True,
            "same_honesty_state": True,
            "source_locked_winner_found": False,
            "already_named_single_theorem_target": True,
        }
        self.assert_code("EXPLORATION_ENTRY_REJECTED_NOT_A_FORK",
                         spine.decide_exploration_entry, request)

    def test_E2_cosmetic_event_is_not_progress(self) -> None:
        self.assert_code("PROGRESS_DELTA_INVALID_COSMETIC",
                         spine.validate_progress_delta,
                         {"kind": "WRAPPER_CREATED"})

    def test_E3_phase_key_smuggling_fails(self) -> None:
        changed = dict(PHASE, source_object_family_id="OTHER_FAMILY")
        self.assert_code("EXPLORATION_PHASE_KEY_SMUGGLE",
                         spine.validate_phase_preservation,
                         PHASE, changed, claimed_same_phase=True)

    def test_E4_two_agent_surrogate_agreement_fails(self) -> None:
        self.assert_code(
            "EXPLORATION_SURROGATE_COLLUSION",
            spine.validate_two_keys,
            {"locally_executable": True, "source_compatible": True},
            {
                "mathematically_honest": True,
                "non_surrogate": True,
                "source_object_not_surrogate": False,
            },
        )

    def test_E5_experimental_import_cannot_enter_production(self) -> None:
        self.assert_code(
            "EXPERIMENTAL_CANONICAL_CONTAMINATION",
            spine.validate_normal_loop_admission,
            {"production_imports_experimental": True},
        )

    def test_E6_non_px_rh_owner_deferral_fails(self) -> None:
        self.assert_code(
            "MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH",
            spine.resolve_owner_boundary,
            decision="CANONICAL_DEFINITION_MINT",
            request_owner=True,
        )

    def test_E7_unstructured_owner_choice_fails(self) -> None:
        self.assert_code(
            "PROSHKA_UNSTRUCTURED_OWNER_DEFERRAL",
            spine.validate_proshka_operative_class,
            "owner choose A or B",
        )

    def test_E8_hard_stall_review_cannot_fan_out(self) -> None:
        self.assert_code(
            "EXPLORATION_CHAT_FANOUT",
            spine.validate_exploration_review,
            {
                "fresh_chat": True,
                "full_context_reupload": False,
                "state": "HARD_STALL",
                "review_count_for_episode": 0,
                "review_count_for_phase_blocker": 0,
                "ordinary_goal_close_as_sole_trigger": False,
            },
        )

    def test_E9_unvalidated_delta_cannot_reset_stall(self) -> None:
        cosmetic = valid_delta(
            kind="BLOCKER_DECOMPOSED",
            verifier="CONDITIONAL",
            validated=False,
            stall_counter_reset=True,
        )
        self.assert_code("STALL_COUNTER_RESET_INVALID",
                         spine.validate_progress_delta, cosmetic)

    def test_E10_renamed_route_cannot_restart(self) -> None:
        route = candidate("A", "NORMALIZED_SHAPE")
        previous = {spine.route_fingerprint(route)}
        renamed = dict(route, route_id="NEW_NAME", file_path="new_file.lean")
        self.assert_code("EXPLORATION_ALIAS_RESTART",
                         spine.ensure_no_alias_restart, previous, renamed)

    def test_E11_counterexample_is_real_progress(self) -> None:
        result = spine.validate_progress_delta(valid_delta())
        self.assertEqual(result["result"], "VALID_PROGRESS_DELTA")
        self.assertTrue(result["stall_counter_reset"])
        self.assertTrue(result["candidate_set_shrunk"])

    def test_E12_time_is_warning_only(self) -> None:
        result = spine.stall_decision(
            no_progress_streak=2,
            total_cycles=2,
            active_reasoning_seconds=8 * 60 * 60,
            proshka_review_count=0,
        )
        self.assertEqual(result["state"], "LOCAL_EXPLORATION")
        self.assertFalse(result["proshka_call"])
        self.assertEqual(result["warnings"], ["EXPLORATION_TIME_BUDGET_WARNING"])

    def test_E13_px_rh_claim_is_the_single_owner_boundary(self) -> None:
        result = spine.resolve_owner_boundary(
            decision="PX_RH_CLAIM", request_owner=True)
        self.assertEqual(result["operative_class"],
                         "OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM")

    def test_E14_operational_gate_does_not_reopen_mathematics(self) -> None:
        result = spine.resolve_owner_boundary(
            decision="ROUTE_SELECTED",
            request_owner=False,
            operational_action="COMMIT_OR_PUSH",
        )
        self.assertEqual(
            result["mathematical_state"],
            "DELEGATED_MATHEMATICAL_DECISION_REMAINS_SELECTED",
        )
        self.assertEqual(result["operational_state"], "OPERATIONAL_ACTION_PENDING")
        self.assertFalse(result["owner_mathematical_action_required"])

    def test_only_px_rh_owner_operative_class_is_allowed(self) -> None:
        self.assertEqual(
            spine.validate_proshka_operative_class(
                "OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM"),
            "OWNER_AUTHORITY_REQUIRED_PX_RH_CLAIM",
        )
        self.assert_code(
            "MATHEMATICAL_OWNER_DEFERRAL_OUTSIDE_PX_RH",
            spine.validate_proshka_operative_class,
            "OWNER_AUTHORITY_REQUIRED_ROUTE_PROMOTION",
        )

    def test_phase_change_is_delegated_not_owner_deferred(self) -> None:
        changed = dict(PHASE, front_id="NEXT_FRONT")
        self.assertEqual(
            spine.validate_phase_preservation(PHASE, changed, claimed_same_phase=False),
            "DELEGATED_PHASE_CHANGE_REQUIRED",
        )
        result = spine.resolve_owner_boundary(
            decision="PHASE_FRONT_CHANGE", request_owner=False)
        self.assertEqual(
            result["mathematical_state"],
            "DELEGATED_MATHEMATICAL_DECISION_REMAINS_SELECTED",
        )

    def test_review_gate_and_budget(self) -> None:
        call = {
            "fresh_chat": False,
            "full_context_reupload": False,
            "state": "REVIEW_READY",
            "review_count_for_episode": 0,
            "review_count_for_phase_blocker": 0,
            "ordinary_goal_close_as_sole_trigger": False,
        }
        self.assertEqual(spine.validate_exploration_review(call),
                         "EXPLORATION_REVIEW_ALLOWED")
        duplicate = dict(call, review_count_for_episode=1)
        self.assert_code("EXPLORATION_REVIEW_DUPLICATE",
                         spine.validate_exploration_review, duplicate)


class RuntimeAndSpineTests(unittest.TestCase):
    def test_initial_runtime_schema_and_active_control(self) -> None:
        result = spine.validate_p9a()
        self.assertEqual(result["control"], "ACTIVE")
        self.assertEqual(result["authority"],
                         "CODEX_PROSHKA_FULL_EXCEPT_PX_RH_CLAIM")

    def test_spine_render_is_deterministic(self) -> None:
        first = spine.build()
        second = spine.build()
        self.assertEqual(first, second)
        self.assertIn("## Staleness warnings", first)
        self.assertNotIn("## Staleness warnings\n- none detected", first)
        self.assertIn("Behavior controls (P9 active)", first)
        self.assertIn("Phase chat and bounded exploration", first)
        self.assertNotIn("candidate brainstorm", first)

    def test_runtime_file_is_canonical_json(self) -> None:
        raw = spine.CHANNEL_RUNTIME.read_text(encoding="utf-8")
        data = json.loads(raw)
        spine.validate_runtime(data)
        canonical = json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
        self.assertEqual(raw, canonical)

    def test_runtime_cannot_claim_an_unplanted_control_state(self) -> None:
        data = json.loads(spine.CHANNEL_RUNTIME.read_text(encoding="utf-8"))
        data["control_status"] = "STAGED"
        with self.assertRaises(spine.ControlViolation) as caught:
            spine.validate_runtime(data)
        self.assertEqual(caught.exception.code, "EXPLORATION_CONTOUR_ORPHANED")

    def test_BCS_P1_duplicate_active_executor_control_fails(self) -> None:
        data = json.loads(spine.BEHAVIOR_REGISTRY.read_text(encoding="utf-8"))
        duplicate = dict(next(
            row for row in data["controls"] if row["body"] == "CODEX_EXECUTOR"
        ))
        duplicate["control_id"] = "DUPLICATE_EXECUTOR"
        data["controls"].append(duplicate)
        with self.assertRaises(spine.ControlViolation) as caught:
            spine.validate_behavior_registry(data)
        self.assertEqual(caught.exception.code, "BEHAVIOR_CONTROL_MULTIPLE_ACTIVE")

    def test_BCS_P2_trigger_owner_missing_fails(self) -> None:
        data = json.loads(spine.BEHAVIOR_REGISTRY.read_text(encoding="utf-8"))
        executor = next(
            row for row in data["controls"] if row["body"] == "CODEX_EXECUTOR"
        )
        executor["trigger_owner"] = ""
        with self.assertRaises(spine.ControlViolation) as caught:
            spine.validate_behavior_registry(data)
        self.assertEqual(caught.exception.code, "BEHAVIOR_TRIGGER_OWNER_MISSING")

    def test_BCS_P3_thin_pointer_cannot_contain_chat_policy(self) -> None:
        text = "Canonical: docs/CODEX_CONTROL.md\nOpen a fresh chat per goal.\n"
        with self.assertRaises(spine.ControlViolation) as caught:
            spine.validate_thin_pointer_text(text, "mutated AGENTS.md")
        self.assertEqual(caught.exception.code, "THIN_POINTER_CONTAINS_POLICY")

    def test_BCS_P4_codex_bootstrap_ignores_claude_policy(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            repo.joinpath("AGENTS.md").write_text(
                "Canonical: docs/CODEX_CONTROL.md\n", encoding="utf-8"
            )
            repo.joinpath("CLAUDE.md").write_text(
                "Independent Claude policy.\n" * 100, encoding="utf-8"
            )
            self.assertEqual(
                spine.validate_codex_bootstrap(repo=repo),
                "CODEX_BOOTSTRAP_VALID",
            )

    def test_SWITCH_P1_codex_resolves_one_control(self) -> None:
        controls = spine.validate_behavior_registry()
        executor = [row for row in controls if row["body"] == "CODEX_EXECUTOR"]
        self.assertEqual(len(executor), 1)
        self.assertEqual(executor[0]["path"], "docs/CODEX_CONTROL.md")

    def test_chat_plants_same_phase_continue(self) -> None:
        runtime = json.loads(spine.CHANNEL_RUNTIME.read_text(encoding="utf-8"))
        phase = runtime["active_proshka_phase"]["phase_key"]
        for event in ("NEW_GOAL", "SESSION_RESTART", "FIVE_HOURS", "SITE_BATON", "MINT"):
            self.assertEqual(
                spine.decide_phase_chat(runtime, phase, event=event),
                "CONTINUE_EXISTING_CHAT",
            )

    def test_old_runtime_record_warns_but_does_not_open_a_fresh_chat(self) -> None:
        runtime = json.loads(spine.CHANNEL_RUNTIME.read_text(encoding="utf-8"))
        runtime["active_proshka_phase"]["opened_at"] = "2020-01-01T00:00:00+00:00"
        phase = runtime["active_proshka_phase"]["phase_key"]
        self.assertEqual(
            spine.decide_phase_chat(runtime, phase, event="SESSION_RESTART"),
            "CONTINUE_EXISTING_CHAT",
        )
        with mock.patch.object(spine, "_read_runtime", return_value=runtime):
            warnings = spine._staleness_warnings()
        self.assertTrue(any("Age alone never authorizes a fresh chat" in row
                            for row in warnings))

    def test_chat_plant_changed_front_opens_after_close(self) -> None:
        runtime = json.loads(spine.CHANNEL_RUNTIME.read_text(encoding="utf-8"))
        changed = dict(runtime["active_proshka_phase"]["phase_key"], front_id="NEXT_FRONT")
        self.assertEqual(
            spine.decide_phase_chat(
                runtime, changed, event="FRONT_CHANGE", phase_change_ratified=True,
            ),
            "CLOSE_OLD_OPEN_NEW_PHASE_CHAT",
        )

    def test_chat_plant_fatal_closes_immediately(self) -> None:
        runtime = json.loads(spine.CHANNEL_RUNTIME.read_text(encoding="utf-8"))
        phase = runtime["active_proshka_phase"]["phase_key"]
        self.assertEqual(
            spine.decide_phase_chat(runtime, phase, event="FATAL"),
            "CLOSE_PHASE_IMMEDIATELY",
        )

    def test_chat_plant_missing_handle_fails_closed(self) -> None:
        runtime = json.loads(spine.CHANNEL_RUNTIME.read_text(encoding="utf-8"))
        runtime["active_proshka_phase"]["conversation_id"] = ""
        with self.assertRaises(spine.ControlViolation) as caught:
            spine.decide_phase_chat(
                runtime, runtime["active_proshka_phase"]["phase_key"], event="NEW_GOAL",
            )
        self.assertEqual(caught.exception.code, "PROSHKA_CHAT_HANDLE_LOST")

    def test_machine_views_are_deterministic(self) -> None:
        first = spine.build_state()
        second = spine.build_state()
        self.assertEqual(first, second)
        self.assertEqual(first["schema"], "q3_spine_state.v1")
        self.assertEqual(first["meta_corpus"]["schema"], "q3_meta_corpus.v1")

    def test_four_database_roles_are_explicit_and_not_merged(self) -> None:
        control = spine.CONTROL.read_text(encoding="utf-8")
        self.assertIn("q3.lean.aristotle/aristotle_db/knowledge.db", control)
        self.assertIn("q3.lean.aristotle/aristotle_db/aristotle_proofs.db", control)
        self.assertIn("q3.lean.aristotle/aristotle_db/observability.db", control)
        self.assertIn("~/.codex/memories_1.sqlite", control)
        self.assertIn("PROJECT_DATABASES_MUST_NOT_BE_MERGED", control)
        self.assertIn("NATIVE_MEMORY_SEMANTIC_OVERRIDE", control)
        self.assertIn("OBSERVABILITY_SNAPSHOT_INVALID", control)
        self.assertEqual(spine.validate_p9a()["runtime"], "VALID")


class KnowledgeCloseoutTests(unittest.TestCase):
    def test_closeout_and_link_are_one_temporary_transaction(self) -> None:
        production_before = hashlib.sha256(kb.REPO.joinpath(
            "q3.lean.aristotle/aristotle_db/knowledge.db").read_bytes()).hexdigest()
        with tempfile.TemporaryDirectory() as tmp:
            db_path = Path(tmp) / "knowledge.db"
            conn = sqlite3.connect(db_path)
            conn.row_factory = sqlite3.Row
            conn.execute("PRAGMA foreign_keys = ON")
            conn.executescript(kb.SCHEMA.read_text(encoding="utf-8"))
            conn.execute(
                "INSERT INTO move (id,name,provenance_layer,source_file) VALUES (?,?,?,?)",
                ("MOVE_1", "temporary move", "arsenal", "temporary fixture"),
            )
            conn.commit()

            kb.record_exploration_close(
                conn,
                entry_id="EXP_CLOSE_1",
                recorded_date="2026-08-05",
                state="selected",
                title="Temporary exploration close",
                target="BLOCKER_1",
                validation="DELTA_1:PAPER",
                artifact_sha="b" * 64,
                next_target="ROUTE_A",
                body="Selected ROUTE_A; rollback ROUTE_B; experimental and not promoted.",
                source_file="temporary fixture",
                links=(("move", "MOVE_1", "applies_move", "fixture link"),),
            )
            self.assertEqual(conn.execute(
                "SELECT COUNT(*) FROM journal_entry WHERE kind='exploration_close'"
            ).fetchone()[0], 1)
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM link").fetchone()[0], 1)
            self.assertEqual(conn.execute("SELECT COUNT(*) FROM journal_fts").fetchone()[0], 1)

            with self.assertRaises(sqlite3.IntegrityError):
                kb.record_exploration_close(
                    conn,
                    entry_id="EXP_CLOSE_1",
                    recorded_date="2026-08-05",
                    state="selected",
                    title="Must not overwrite",
                    target="BLOCKER_1",
                    validation="DELTA_1:PAPER",
                    artifact_sha="c" * 64,
                    next_target="ROUTE_A",
                    body="Duplicate id must roll back.",
                    source_file="temporary fixture",
                )
            self.assertEqual(conn.execute(
                "SELECT COUNT(*) FROM journal_entry WHERE id='EXP_CLOSE_1'"
            ).fetchone()[0], 1)
            conn.close()

        production_after = hashlib.sha256(kb.REPO.joinpath(
            "q3.lean.aristotle/aristotle_db/knowledge.db").read_bytes()).hexdigest()
        self.assertEqual(production_before, production_after)


if __name__ == "__main__":
    unittest.main()
