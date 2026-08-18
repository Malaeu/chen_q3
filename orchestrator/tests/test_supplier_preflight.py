"""Plants for the complete shelf, EnvDump properties, and generic type-fit chain."""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from docs.cartographer.comparator import fit
from scripts import supplier_preflight


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


def fake_external(matches: list[dict[str, object]] | None = None) -> SimpleNamespace:
    return SimpleNamespace(
        search_registry=lambda _query: {
            "schema": "q3_external_lean_search.v2",
            "enabled_bases": ["zeta23"],
            "bases_queried": ["zeta23"],
            "matches": matches or [],
            "errors": [],
        }
    )


def fake_fit(*, freshness: str = "PASS") -> SimpleNamespace:
    class FakeFitError(ValueError):
        code = "DECLARATION_NOT_FOUND"

    def unresolved(_name: str, _index: object) -> object:
        raise FakeFitError("DECLARATION_NOT_FOUND")

    return SimpleNamespace(
        FitError=FakeFitError,
        environment_freshness=lambda: {
            "status": freshness,
            "refresh_command": fit.ENVDUMP_COMMAND if freshness != "PASS" else None,
        },
        load_index=lambda: {},
        resolve_declaration=unresolved,
        source_declaration_candidates=lambda _name: [],
        declaration_properties=lambda name, row: {"name": name, **row},
    )


def test_stale_environment_is_incomplete_and_prints_exact_command(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        supplier_preflight, "run_shelf", lambda _query: {"status": "HITS", "returncode": 0}
    )
    modules = iter([fake_external(), fake_fit(freshness="INCOMPLETE")])
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: next(modules))
    result = supplier_preflight.run_preflight("supplier")
    assert result["status"] == "INCOMPLETE"
    assert result["refresh_command"] == fit.ENVDUMP_COMMAND


def test_foreign_exact_declaration_is_not_claimed_as_local_fit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        supplier_preflight, "run_shelf", lambda _query: {"status": "HITS", "returncode": 0}
    )
    external = fake_external(
        [
            {
                "base_id": "zeta23",
                "match_kind": "EXACT_DECLARATION",
                "declaration_name": "xiPrime_zeros_in_open_critical_strip",
            }
        ]
    )
    modules = iter([external, fake_fit()])
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: next(modules))
    result = supplier_preflight.run_preflight(
        "xiPrime_zeros_in_open_critical_strip",
        candidate="xiPrime_zeros_in_open_critical_strip",
    )
    assert result["status"] == "FOREIGN_UNVERIFIED"


def test_complete_absence_requires_complete_shelf_and_no_foreign_match(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        supplier_preflight,
        "run_shelf",
        lambda _query: {"status": "COMPLETE_ABSENCE", "returncode": 1},
    )
    modules = iter([fake_external(), fake_fit()])
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: next(modules))
    result = supplier_preflight.run_preflight("guaranteed_missing_declaration_xyz")
    assert result["status"] == "COMPLETE_ABSENCE"


def test_exact_declaration_absence_ignores_prose_only_candidates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        supplier_preflight, "run_shelf", lambda _query: {"status": "HITS", "returncode": 0}
    )
    modules = iter([fake_external(), fake_fit()])
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: next(modules))
    result = supplier_preflight.run_preflight(
        "guaranteed_missing_declaration_xyz",
        candidate="guaranteed_missing_declaration_xyz",
    )
    assert result["status"] == "COMPLETE_ABSENCE"
    assert result["prose_candidates_present"] is True


def test_source_only_q3_or_mathlib_declaration_remains_candidate_only(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        supplier_preflight, "run_shelf", lambda _query: {"status": "HITS", "returncode": 0}
    )
    fit_module = fake_fit()
    fit_module.source_declaration_candidates = lambda _name: [
        {"source": "mathlib", "file": "Mathlib/Example.lean", "line": 1}
    ]
    modules = iter([fake_external(), fit_module])
    monkeypatch.setattr(supplier_preflight, "_load_module", lambda *_args: next(modules))
    result = supplier_preflight.run_preflight("Mathlib.example", candidate="Mathlib.example")
    assert result["status"] == "CANDIDATE_ONLY"
    assert result["source_candidates"][0]["source"] == "mathlib"
