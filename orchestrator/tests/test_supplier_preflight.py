"""Plants for the complete shelf, EnvDump properties, and generic type-fit chain."""

from __future__ import annotations

import json
import subprocess
from types import SimpleNamespace

import pytest

from docs.cartographer.comparator import fit
from scripts import supplier_preflight


def test_external_process_receipt_is_bound_to_exact_request(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = {
        "schema": supplier_preflight.EXTERNAL_SCHEMA,
        "query": "different query",
        "query_sha256": "0" * 64,
        "candidate": "Q3.wrong",
        "candidate_sha256": "0" * 64,
        "candidate_provenance": "SOURCE_DECLARED",
        "budget_seconds": 15,
        "enabled_bases": [],
        "bases_queried": [],
        "base_results": [],
        "matches": [],
        "terms": ["different"],
        "registry_sha256": "0" * 64,
        "errors": [],
        "boundary": "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE",
    }
    monkeypatch.setattr(
        supplier_preflight.subprocess,
        "run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess(
            args=[], returncode=0, stdout=json.dumps(payload), stderr=""
        ),
    )
    result = supplier_preflight.run_external(
        "exact query",
        candidate="Q3.expected",
        candidate_provenance="SOURCE_DECLARED",
    )
    assert result["error"] is not None
    assert "receipt invalid" in str(result["error"])


def test_ask_shelf_preserves_utf8_when_truncating_long_lean_matches() -> None:
    proc = subprocess.run(
        [
            str(supplier_preflight.ASK),
            "selectedFerrersPreAnchorIndex N less than "
            "sourceWeilEvenTailCutoff W02 norm lower bound",
        ],
        cwd=supplier_preflight.REPO,
        capture_output=True,
        text=False,
        check=False,
    )
    assert proc.returncode in {0, 1, 2}
    proc.stdout.decode("utf-8")
    proc.stderr.decode("utf-8")


def record(name: str, module: str = "Q3.Proofs.RouteB.Sample") -> dict[str, object]:
    return {
        "name": name,
        "kind": "theorem",
        "type": "True",
        "levelParams": [],
        "numBinders": 0,
        "file": module,
        "line": "1",
        "doc": "",
        "typeConsts": [],
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
        "isPrivate": False,
        "isUnsafe": False,
    }


def test_resolve_declaration_accepts_full_name_and_unique_basename() -> None:
    index = {"Q3.RouteB.exact": record("Q3.RouteB.exact")}
    assert fit.resolve_declaration("Q3.RouteB.exact", index)[0] == "Q3.RouteB.exact"
    assert fit.resolve_declaration("exact", index)[0] == "Q3.RouteB.exact"


def test_resolve_declaration_rejects_ambiguous_basename() -> None:
    index = {
        "Q3.RouteB.Left.same": record("Q3.RouteB.Left.same"),
        "Q3.RouteB.Right.same": record("Q3.RouteB.Right.same"),
    }
    with pytest.raises(fit.FitError, match="DECLARATION_AMBIGUOUS"):
        fit.resolve_declaration("same", index)


def test_harness_uses_target_term_type_and_both_modules() -> None:
    candidate = record("Q3.RouteB.supplier", "Q3.Proofs.RouteB.Supplier")
    target = record("Q3.RouteB.target", "Q3.Proofs.RouteB.Target")
    target["type"] = "∀ n : Nat, n = n"
    source = fit._harness_source(
        "Q3.RouteB.supplier", candidate, "Q3.RouteB.target", target
    )
    assert "import Q3.Proofs.RouteB.Supplier" in source
    assert "import Q3.Proofs.RouteB.Target" in source
    assert "q3ComparatorExpectedType _ (@Q3.RouteB.target)" in source
    assert "exact (@Q3.RouteB.supplier)" in source
    assert str(target["type"]) not in source


def external_payload(*, exact: str = "ABSENT") -> dict[str, object]:
    boundary = (
        supplier_preflight.SOURCE_ABSENCE_SCOPE
        if exact == "ABSENT"
        else "SOURCE_DECLARATION_PRESENT"
    )
    return {
        "schema": supplier_preflight.EXTERNAL_SCHEMA,
        "enabled_bases": ["zeta23"],
        "bases_queried": ["zeta23"],
        "matches": [],
        "errors": [],
        "boundary": "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE",
        "base_results": [
            {
                "base_id": "zeta23",
                "exact_candidate": {
                    "status": exact,
                    "boundary": boundary,
                    "searched_regular_source_count": 12,
                },
            }
        ],
    }


def external_run(*, exact: str = "ABSENT") -> dict[str, object]:
    payload = external_payload(exact=exact)
    return {
        "returncode": 0,
        "stdout": __import__("json").dumps(payload),
        "stderr": "",
        "duration_ms": 1,
        "payload": payload,
        "error": None,
    }


def patch_retrieval(
    monkeypatch: pytest.MonkeyPatch, *, shelf: str = "HITS", exact: str = "ABSENT"
) -> None:
    monkeypatch.setattr(
        supplier_preflight,
        "run_external",
        lambda *_args, **_kwargs: external_run(exact=exact),
    )
    monkeypatch.setattr(
        supplier_preflight,
        "run_shelf",
        lambda _query, **_kwargs: {
            "status": shelf,
            "returncode": {"HITS": 0, "SHELF_ABSENCE": 1, "INCOMPLETE": 2}[shelf],
        },
    )


def fake_fit(
    *, freshness: str = "PASS", resolved: bool = False, fit_status: str = "EXACT_FIT"
) -> SimpleNamespace:
    class FakeFitError(ValueError):
        code = "DECLARATION_NOT_FOUND"

    def resolve(name: str, _index: object) -> object:
        if not resolved:
            raise FakeFitError("DECLARATION_NOT_FOUND")
        return name, record(name)

    return SimpleNamespace(
        FitError=FakeFitError,
        environment_freshness=lambda: {
            "status": freshness,
            "refresh_command": fit.ENVDUMP_COMMAND if freshness != "PASS" else None,
        },
        load_index=lambda: {},
        resolve_declaration=resolve,
        source_declaration_candidates=lambda _name: [],
        declaration_properties=lambda name, row: {"name": name, **row},
        direct_type_fit=lambda _candidate, _target: {"status": fit_status},
    )


def test_stale_environment_is_incomplete_and_prints_exact_command(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    monkeypatch.setattr(
        supplier_preflight,
        "_load_module",
        lambda *_args: fake_fit(freshness="INCOMPLETE"),
    )
    result = supplier_preflight.run_preflight("supplier", candidate="candidate")
    assert result["status"] == "INCOMPLETE"
    assert result["environment"]["refresh_command"] == fit.ENVDUMP_COMMAND


def test_foreign_exact_declaration_is_not_claimed_as_local_fit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch, exact="PRESENT")
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fake_fit())
    result = supplier_preflight.run_preflight(
        "xiPrime_zeros_in_open_critical_strip",
        candidate="xiPrime_zeros_in_open_critical_strip",
    )
    assert result["status"] == "FOREIGN_UNVERIFIED"


def test_query_only_shelf_absence_requires_precise_candidate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch, shelf="SHELF_ABSENCE")
    result = supplier_preflight.run_preflight("guaranteed_missing_declaration_xyz")
    assert result["status"] == "INCOMPLETE"
    assert result["reason"] == "PRECISE_CANDIDATE_REQUIRED_FOR_COMPLETE_ABSENCE"


def test_exact_declaration_absence_ignores_prose_only_candidates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fake_fit())
    result = supplier_preflight.run_preflight(
        "guaranteed_missing_declaration_xyz",
        candidate="guaranteed_missing_declaration_xyz",
        candidate_provenance="SOURCE_DECLARED",
    )
    assert result["status"] == "COMPLETE_ABSENCE"
    assert result["prose_candidates_present"] is True
    assert result["source_absence_scope"] == "SOURCE_DECLARATION_ABSENCE"


def test_source_only_q3_or_mathlib_declaration_remains_candidate_only(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    fit_module = fake_fit()
    fit_module.source_declaration_candidates = lambda _name: [
        {"source": "mathlib", "file": "Mathlib/Example.lean", "line": 1}
    ]
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fit_module)
    result = supplier_preflight.run_preflight("Mathlib.example", candidate="Mathlib.example")
    assert result["status"] == "CANDIDATE_ONLY"
    assert result["source_candidates"][0]["source"] == "mathlib"


def test_generated_candidate_miss_never_claims_source_absence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch, shelf="SHELF_ABSENCE")
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: fake_fit())
    result = supplier_preflight.run_preflight(
        "missing projection",
        candidate="Q3.missingProjection",
        candidate_provenance="GENERATED_OR_DERIVED",
    )
    assert result["status"] == "INCOMPLETE"
    assert result["reason"] == "ELABORATED_EXTERNAL_DECLARATION_LOOKUP_REQUIRED"
    assert result["source_absence_scope"] is None


def test_exact_fit_is_preserved_only_from_direct_comparator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    patch_retrieval(monkeypatch)
    monkeypatch.setattr(
        supplier_preflight,
        "_load_module",
        lambda *_args: fake_fit(resolved=True, fit_status="EXACT_FIT"),
    )
    result = supplier_preflight.run_preflight(
        "supplier",
        candidate="Q3.RouteB.supplier",
        target="Q3.RouteB.target",
        candidate_provenance="SOURCE_DECLARED",
    )
    assert result["status"] == "EXACT_FIT"
    assert result["comparison"] == {"status": "EXACT_FIT"}


def test_external_receipt_is_mode_0600_and_removed_after_shelf(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed: list[tuple[object, int]] = []
    monkeypatch.setattr(
        supplier_preflight,
        "run_external",
        lambda *_args, **_kwargs: external_run(),
    )

    def inspect_receipt(_query: str, *, external_receipt, **_kwargs):
        observed.append(
            (external_receipt, external_receipt.stat().st_mode & 0o777)
        )
        assert external_receipt.parent != supplier_preflight.REPO
        return {"status": "HITS", "returncode": 0}

    monkeypatch.setattr(supplier_preflight, "run_shelf", inspect_receipt)
    result = supplier_preflight.run_preflight("supplier")
    assert result["status"] == "CANDIDATE_ONLY"
    assert observed[0][1] == 0o600
    assert not observed[0][0].exists()


def test_receipt_is_removed_when_shelf_raises(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed = []
    monkeypatch.setattr(
        supplier_preflight,
        "run_external",
        lambda *_args, **_kwargs: external_run(),
    )

    def fail(_query: str, *, external_receipt, **_kwargs):
        observed.append(external_receipt)
        raise OSError("plant")

    monkeypatch.setattr(supplier_preflight, "run_shelf", fail)
    result = supplier_preflight.run_preflight("supplier")
    assert result["status"] == "INCOMPLETE"
    assert not observed[0].exists()
