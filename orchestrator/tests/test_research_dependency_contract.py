from __future__ import annotations

import copy
import unittest

from orchestrator import research_dependency_contract, session_briefing


def row() -> dict:
    return copy.deepcopy(session_briefing.validate_registry(session_briefing.REPO)["debts"][0])


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


if __name__ == "__main__":
    unittest.main()
