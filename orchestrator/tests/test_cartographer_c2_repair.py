from __future__ import annotations

import json
import sqlite3
from pathlib import Path

import pytest

from docs.cartographer import atoms, map_coverage
from docs.cartographer import inventory as inventory_module
from orchestrator import kb_migrate_route058 as route058

ROUTEB_REL = Path("q3.lean.aristotle/Q3/Proofs/RouteB")


def write_lean(repo: Path, relative: str, declaration: str) -> None:
    path = repo / ROUTEB_REL / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"theorem {declaration} : True := by\n  exact External.magic_fact\n",
        encoding="utf-8",
    )


def write_inventory(repo: Path, path: Path) -> dict:
    items, files = inventory_module.scan(repo, "RouteB")
    payload = {"scope": "RouteB", "files_scanned": files, "items": items}
    path.write_text(json.dumps(payload), encoding="utf-8")
    return payload


def write_doc(repo: Path, relative: str, text: str) -> Path:
    path = repo / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def declaration_in_docs(repo: Path, declaration: str) -> bool:
    result = inventory_module.build_inventory(repo, "RouteB")
    item = next(entry for entry in result["items"] if entry["name"] == declaration)
    return item["in_docs"]


def test_atoms_recursive_ids_collision_and_bare_list(tmp_path: Path) -> None:
    write_lean(tmp_path, "Top.lean", "TopThing")
    write_lean(tmp_path, "Core.lean", "RootCoreThing")
    write_lean(tmp_path, "MuntzV3/Core.lean", "NestedCoreThing")
    inventory_path = tmp_path / "inventory.json"
    write_inventory(tmp_path, inventory_path)
    output = tmp_path / "atoms.json"

    rows = atoms.generate(tmp_path, inventory_path, output)

    assert isinstance(json.loads(output.read_text(encoding="utf-8")), list)
    assert all(set(row) == {"atom", "n_files", "files"} for row in rows)
    magic = next(row for row in rows if row["atom"] == "External.magic_fact")
    assert magic["files"] == ["Core.lean", "MuntzV3/Core.lean", "Top.lean"]
    assert magic["n_files"] == 3


def test_atoms_inventory_count_drift_preserves_output(tmp_path: Path) -> None:
    write_lean(tmp_path, "Top.lean", "TopThing")
    write_lean(tmp_path, "MuntzV3/Core.lean", "NestedCoreThing")
    inventory_path = tmp_path / "inventory.json"
    payload = write_inventory(tmp_path, inventory_path)
    payload["files_scanned"] = 1
    inventory_path.write_text(json.dumps(payload), encoding="utf-8")
    output = tmp_path / "atoms.json"
    output.write_text("sentinel", encoding="utf-8")

    with pytest.raises(atoms.AtomIndexError, match="denominator drift"):
        atoms.generate(tmp_path, inventory_path, output)
    assert output.read_text(encoding="utf-8") == "sentinel"


def test_atoms_inventory_boolean_denominator_preserves_output(tmp_path: Path) -> None:
    write_lean(tmp_path, "Top.lean", "TopThing")
    inventory_path = tmp_path / "inventory.json"
    payload = write_inventory(tmp_path, inventory_path)
    payload["files_scanned"] = True
    inventory_path.write_text(json.dumps(payload), encoding="utf-8")
    output = tmp_path / "atoms.json"
    output.write_text("sentinel", encoding="utf-8")

    with pytest.raises(atoms.AtomIndexError, match="denominator drift"):
        atoms.generate(tmp_path, inventory_path, output)
    assert output.read_text(encoding="utf-8") == "sentinel"


def test_atoms_same_count_declaration_drift_preserves_output(tmp_path: Path) -> None:
    write_lean(tmp_path, "Top.lean", "TopThing")
    write_lean(tmp_path, "MuntzV3/Core.lean", "NestedCoreThing")
    inventory_path = tmp_path / "inventory.json"
    payload = write_inventory(tmp_path, inventory_path)
    payload["items"][0]["signature"] += " changed"
    inventory_path.write_text(json.dumps(payload), encoding="utf-8")
    output = tmp_path / "atoms.json"
    output.write_text("sentinel", encoding="utf-8")

    with pytest.raises(atoms.AtomIndexError, match="projection drift"):
        atoms.generate(tmp_path, inventory_path, output)
    assert output.read_text(encoding="utf-8") == "sentinel"


@pytest.mark.parametrize("invalid_line", [True, 1.0])
def test_atoms_line_type_drift_preserves_output(
    tmp_path: Path,
    invalid_line: object,
) -> None:
    write_lean(tmp_path, "Top.lean", "TopThing")
    inventory_path = tmp_path / "inventory.json"
    payload = write_inventory(tmp_path, inventory_path)
    payload["items"][0]["line"] = invalid_line
    inventory_path.write_text(json.dumps(payload), encoding="utf-8")
    output = tmp_path / "atoms.json"
    output.write_text("sentinel", encoding="utf-8")

    with pytest.raises(atoms.AtomIndexError, match="field=line"):
        atoms.generate(tmp_path, inventory_path, output)
    assert output.read_text(encoding="utf-8") == "sentinel"


def test_atoms_empty_source_fails_without_output(tmp_path: Path) -> None:
    (tmp_path / ROUTEB_REL).mkdir(parents=True)
    inventory_path = tmp_path / "inventory.json"
    inventory_path.write_text('{"scope":"RouteB","files_scanned":0,"items":[]}', encoding="utf-8")
    output = tmp_path / "atoms.json"

    with pytest.raises(atoms.AtomIndexError, match="empty"):
        atoms.generate(tmp_path, inventory_path, output)
    assert not output.exists()


def test_atoms_publication_uses_atomic_replace(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    output = tmp_path / "atoms.json"
    calls: list[tuple[Path, Path]] = []
    original_replace = atoms.os.replace

    def observed_replace(source: Path, destination: Path) -> None:
        calls.append((Path(source), Path(destination)))
        original_replace(source, destination)

    monkeypatch.setattr(atoms.os, "replace", observed_replace)
    atoms.atomic_write_json(output, [{"atom": "A.b", "n_files": 1, "files": ["Top.lean"]}])

    assert len(calls) == 1
    assert calls[0][1] == output
    assert json.loads(output.read_text(encoding="utf-8"))[0]["atom"] == "A.b"


def test_atoms_positional_cli_is_preserved() -> None:
    args = atoms.parse_args(["custom.json"])
    assert args.output == "custom.json"


ASSEMBLY_SCHEMA = """
create table assembly (
  chain text not null,
  step integer not null,
  requirement text not null,
  required_by text,
  supplied_by text,
  supplier_file text,
  supplier_line integer,
  status text not null,
  note text,
  run_id text not null,
  objects text,
  primary key (chain, step, requirement)
)
"""


def route_db(path: Path, rows: list[tuple] | None = None) -> Path:
    con = sqlite3.connect(path)
    con.execute(ASSEMBLY_SCHEMA)
    source = route058.expected_rows() if rows is None else rows
    con.executemany(
        "insert into assembly values (?,?,?,?,?,?,?,?,?,?,?)",
        [(route058.CHAIN, *row) for row in source],
    )
    con.commit()
    con.close()
    return path


def changed(row: tuple, field: int, value: object) -> tuple:
    values = list(row)
    values[field] = value
    return tuple(values)


def test_route058_exact_rows_pass_independent_of_insertion_order(tmp_path: Path) -> None:
    rows = list(reversed(route058.expected_rows()))
    assert route058.check_database(route_db(tmp_path / "exact.db", rows)) == 0


@pytest.mark.parametrize(
    ("field", "value"),
    [
        (0, 9),
        (1, "changed requirement"),
        (2, "changed required_by"),
        (3, "changed supplied_by"),
        (4, "changed/file.lean"),
        (5, None),
        (6, "READY"),
        (7, "changed note"),
        (8, "changed run"),
        (9, "changed objects"),
    ],
)
def test_route058_drift_in_every_persisted_field_fails(
    tmp_path: Path, field: int, value: object,
) -> None:
    rows = route058.expected_rows()
    rows[0] = changed(rows[0], field, value)
    assert route058.check_database(route_db(tmp_path / f"field-{field}.db", rows)) == 1


def test_route058_null_empty_drift_fails(tmp_path: Path) -> None:
    rows = route058.expected_rows()
    rows[4] = changed(rows[4], 4, "")
    assert rows[4][4] is not None
    assert route058.check_database(route_db(tmp_path / "null-empty.db", rows)) == 1


@pytest.mark.parametrize("supplier_line", [None, 342])
def test_route058_supplier_line_341_drift_fails(
    tmp_path: Path,
    supplier_line: int | None,
) -> None:
    rows = route058.expected_rows()
    assert rows[3][5] == 341
    rows[3] = changed(rows[3], 5, supplier_line)
    assert route058.check_database(
        route_db(tmp_path / f"supplier-line-{supplier_line}.db", rows)
    ) == 1


def test_route058_missing_extra_and_duplicate_step_fail(tmp_path: Path) -> None:
    exact = route058.expected_rows()
    assert route058.check_database(route_db(tmp_path / "missing.db", exact[:-1])) == 1

    extra = exact + [changed(exact[-1], 0, 8)]
    assert route058.check_database(route_db(tmp_path / "extra.db", extra)) == 1

    duplicate = exact + [changed(exact[0], 1, "duplicate requirement")]
    assert route058.check_database(route_db(tmp_path / "duplicate.db", duplicate)) == 1


def test_route058_schema_error_is_infrastructure_failure(tmp_path: Path) -> None:
    path = tmp_path / "broken.db"
    sqlite3.connect(path).close()
    assert route058.check_database(path) == 2


@pytest.mark.parametrize(
    "relative",
    [
        "docs/generated/nested/evidence.md",
        "docs/routeB_bus/MAP_COVERAGE.md",
        "docs/TOOLS.md",
        "docs/.lake/packages/pkg/README.md",
    ],
)
def test_inventory_generated_and_volatile_docs_do_not_count(
    tmp_path: Path,
    relative: str,
) -> None:
    write_lean(tmp_path, "Evidence.lean", "GeneratedOnlyEvidence")
    write_doc(tmp_path, relative, "GeneratedOnlyEvidence")
    assert not declaration_in_docs(tmp_path, "GeneratedOnlyEvidence")


@pytest.mark.parametrize(
    "relative",
    [
        "docs/manual.md",
        "q3.lean.aristotle/ACTIVE/manual.md",
        "docs/generatedish/manual.md",
    ],
)
def test_inventory_independent_docs_count(tmp_path: Path, relative: str) -> None:
    write_lean(tmp_path, "Evidence.lean", "IndependentEvidence")
    write_doc(tmp_path, relative, "IndependentEvidence")
    assert declaration_in_docs(tmp_path, "IndependentEvidence")


def test_inventory_symlink_classification(tmp_path: Path) -> None:
    write_lean(tmp_path, "Evidence.lean", "SymlinkEvidence")
    generated = write_doc(
        tmp_path,
        "docs/generated/generated-target.md",
        "SymlinkEvidence",
    )
    alias = tmp_path / "docs/ordinary-alias.md"
    alias.symlink_to(generated)
    assert not declaration_in_docs(tmp_path, "SymlinkEvidence")

    ordinary_target = write_doc(tmp_path, "evidence/ordinary.md", "SymlinkEvidence")
    active_alias = tmp_path / "q3.lean.aristotle/ACTIVE/ordinary-alias.md"
    active_alias.parent.mkdir(parents=True, exist_ok=True)
    active_alias.symlink_to(ordinary_target)
    assert declaration_in_docs(tmp_path, "SymlinkEvidence")


def test_inventory_does_not_follow_directory_symlinks(tmp_path: Path) -> None:
    write_lean(tmp_path, "Evidence.lean", "DirectorySymlinkEvidence")
    write_doc(tmp_path, "evidence-dir/hidden.md", "DirectorySymlinkEvidence")
    docs = tmp_path / "docs"
    docs.mkdir(parents=True, exist_ok=True)
    (docs / "linked-dir").symlink_to(tmp_path / "evidence-dir", target_is_directory=True)
    assert not declaration_in_docs(tmp_path, "DirectorySymlinkEvidence")


@pytest.mark.parametrize("kind", ["broken", "external"])
@pytest.mark.parametrize(
    "relative",
    ["docs/routeB_bus/MAP_COVERAGE.md", "docs/TOOLS.md"],
)
def test_inventory_excluded_unsafe_file_symlink_fails_closed(
    tmp_path: Path,
    kind: str,
    relative: str,
) -> None:
    alias = tmp_path / relative
    alias.parent.mkdir(parents=True, exist_ok=True)
    if kind == "broken":
        alias.symlink_to(tmp_path / "missing.md")
    else:
        outside = tmp_path.parent / f"{tmp_path.name}-outside.md"
        outside.write_text("outside", encoding="utf-8")
        alias.symlink_to(outside)
    with pytest.raises(inventory_module.DocumentationCorpusError):
        inventory_module.documentation_files(tmp_path)


def test_inventory_is_byte_stable_across_map_coverage_generation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    write_lean(tmp_path, "MapEvidence.lean", "MapGeneratedEvidence")
    write_doc(tmp_path, "docs/routeB_bus/MAP.md", "# Empty manual map\n")
    before = inventory_module.inventory_bytes(
        inventory_module.build_inventory(tmp_path, "RouteB")
    )

    monkeypatch.setattr(map_coverage, "REPO", tmp_path)
    monkeypatch.setattr(map_coverage, "ROUTEB", tmp_path / ROUTEB_REL)
    monkeypatch.setattr(map_coverage, "MAP", tmp_path / "docs/routeB_bus/MAP.md")
    monkeypatch.setattr(
        "sys.argv",
        ["map_coverage.py", "--out", "docs/routeB_bus/MAP_COVERAGE.md"],
    )
    assert map_coverage.main() == 0
    assert "MapGeneratedEvidence" in (
        tmp_path / "docs/routeB_bus/MAP_COVERAGE.md"
    ).read_text(encoding="utf-8")

    after = inventory_module.inventory_bytes(
        inventory_module.build_inventory(tmp_path, "RouteB")
    )
    assert before == after


def test_brief_and_tool_manifest_contracts() -> None:
    repo = Path(__file__).resolve().parents[2]
    brief = (repo / "docs/cartographer/brief.py").read_text(encoding="utf-8")
    manifest = (repo / "docs/cartographer/TOOLS.yaml").read_text(encoding="utf-8")

    assert "GENERATOR: docs/cartographer/brief.py" in brief
    assert "codex_specs/cartographer/brief.py" not in brief
    assert "file_id_semantics: ROUTEB_ROOT_RELATIVE_POSIX" in manifest
    assert (
        "coverage_denominator: LIVE_RECURSIVE_SOURCE_PLUS_EXACT_INVENTORY_DECLARATION_PROJECTION"
        in manifest
    )
    assert "drift_exit_nonzero: true" in manifest
    assert "documentation_roots: [docs, q3.lean.aristotle/ACTIVE]" in manifest
    assert "exact_excludes: [docs/routeB_bus/MAP_COVERAGE.md, docs/TOOLS.md]" in manifest
    assert "subtree_excludes: [docs/generated]" in manifest
    assert 'volatile_path_components: [".lake"]' in manifest
    assert "directory_symlinks: DO_NOT_FOLLOW" in manifest
    assert "unsafe_file_symlinks: FAIL_CLOSED" in manifest
