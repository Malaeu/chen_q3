from __future__ import annotations

import copy
import json
import unittest

from orchestrator import research_dependency_contract, session_briefing


def row() -> dict:
    registry = session_briefing.REPO / "docs/routeB_bus/RECHECKABLE_RESEARCH_DEBTS.json"
    value = copy.deepcopy(json.loads(registry.read_text(encoding="utf-8"))["debts"][0])
    # The registry migration is owned separately; keep these contract tests
    # focused while still planting the new mandatory field below.
    value.setdefault("failure_scope", "CURRENT_ATTEMPT")
    return value


def evidence() -> dict[str, str]:
    return {
        "kind": "COUNTEREXAMPLE",
        "path": "docs/evidence.md",
        "commit": "1" * 40,
        "git_blob": "2" * 40,
        "scope": "EXACT_THEOREM_SHAPE",
        "claim": "The named quantified theorem shape is false.",
    }


class ResearchDependencyContractPlants(unittest.TestCase):
    def test_current_registry_contract_passes(self) -> None:
        research_dependency_contract.validate(row())

    def test_named_dependency_without_consumer_fails(self) -> None:
        planted = row()
        planted["actual_consumer_requirement"] = ""
        with self.assertRaisesRegex(research_dependency_contract.DependencyContractError, "RIGID_DEPENDENCY_UNJUSTIFIED"):
            research_dependency_contract.validate(planted)

    def test_necessary_requires_pinned_evidence(self) -> None:
        planted = row()
        planted["original_object_is"] = "PROVED_NECESSARY"
        planted["necessity_evidence"] = []
        with self.assertRaisesRegex(research_dependency_contract.DependencyContractError, "necessity_evidence_required"):
            research_dependency_contract.validate(planted)

    def test_sufficient_only_is_distinct_from_necessary(self) -> None:
        planted = row()
        planted["original_object_is"] = "SUFFICIENT_ONLY"
        planted["necessity_evidence"] = []
        research_dependency_contract.validate(planted)

    def test_evidence_must_be_structured_and_pinned(self) -> None:
        planted = row()
        planted["original_object_is"] = "PROVED_NECESSARY"
        planted["necessity_evidence"] = ["looks necessary"]
        with self.assertRaisesRegex(
            research_dependency_contract.DependencyContractError,
            "RESEARCH_DEPENDENCY_EVIDENCE_INVALID",
        ):
            research_dependency_contract.validate(planted)

    def test_failure_scope_is_mandatory(self) -> None:
        planted = row()
        planted["failure_scope"] = ""
        with self.assertRaisesRegex(
            research_dependency_contract.DependencyContractError,
            "RIGID_DEPENDENCY_UNJUSTIFIED:failure_scope",
        ):
            research_dependency_contract.validate(planted)

    def test_research_debt_requires_reopen_triggers(self) -> None:
        planted = row()
        planted["reopen_triggers"] = []
        with self.assertRaisesRegex(
            research_dependency_contract.DependencyContractError,
            "RESEARCH_DEBT_REOPEN_TRIGGERS_INVALID",
        ):
            research_dependency_contract.validate(planted)

    def test_nonrefutation_never_mints_mathematical_death(self) -> None:
        for failure in ("NO_SOURCE", "FORMALIZATION_COST", "NO_DERIVATION"):
            with self.subTest(failure=failure):
                planted = row()
                planted["epistemic_status"] = "MATHEMATICALLY_DEAD"
                planted["failure_type"] = failure
                with self.assertRaisesRegex(research_dependency_contract.DependencyContractError, "MATHEMATICALLY_DEAD_WITHOUT_IMPOSSIBILITY"):
                    research_dependency_contract.validate(planted)

    def test_counterexample_death_requires_evidence(self) -> None:
        planted = row()
        planted["epistemic_status"] = "MATHEMATICALLY_DEAD"
        planted["failure_type"] = "COUNTEREXAMPLE"
        with self.assertRaisesRegex(research_dependency_contract.DependencyContractError, "MATHEMATICALLY_DEAD_WITHOUT_EVIDENCE"):
            research_dependency_contract.validate(planted)

    def test_counterexample_death_accepts_pinned_scoped_evidence(self) -> None:
        planted = row()
        planted["epistemic_status"] = "MATHEMATICALLY_DEAD"
        planted["failure_type"] = "COUNTEREXAMPLE"
        planted["death_evidence"] = [evidence()]
        research_dependency_contract.validate(planted)

    def test_other_can_never_mint_mathematical_death(self) -> None:
        planted = row()
        planted["epistemic_status"] = "MATHEMATICALLY_DEAD"
        planted["failure_type"] = "OTHER"
        planted["death_evidence"] = [evidence()]
        with self.assertRaisesRegex(
            research_dependency_contract.DependencyContractError,
            "MATHEMATICALLY_DEAD_WITHOUT_IMPOSSIBILITY",
        ):
            research_dependency_contract.validate(planted)


if __name__ == "__main__":
    unittest.main()
