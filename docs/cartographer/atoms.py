#!/usr/bin/env python3
"""Extract external Lean atoms from the complete Route B source tree.

The committed declaration inventory is an input contract, not merely a bag of
names. Atom publication fails closed unless its exact declaration projection
matches a fresh recursive scan of the current Route B sources.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys
import tempfile
from pathlib import Path
from typing import Any

try:
    from . import inventory as inventory_module
except ImportError:  # Direct execution: python3 docs/cartographer/atoms.py ...
    import inventory as inventory_module  # type: ignore[no-redef]


REPO = Path(__file__).resolve().parents[2]
ROUTEB_REL = Path("q3.lean.aristotle/Q3/Proofs/RouteB")
DEFAULT_INVENTORY = Path(__file__).resolve().parent / "inventory_RouteB.json"
PROJECTION_FIELDS = ("kind", "name", "file", "line", "signature")


class AtomIndexError(RuntimeError):
    """Fail-closed atom-index contract violation."""


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")

NOISE = set("""theorem lemma def abbrev structure instance example noncomputable private
protected open namespace end section variable universe import set_option attribute
by exact apply refine intro intros have show from fun let in with at using this
simp simpa rw rwa unfold change calc constructor rcases obtain cases induction
match do return if then else fun_prop norm_num omega ring linarith nlinarith
push_neg field_simp positivity decide native_decide trivial rfl sorry
Type Prop Sort ℂ ℝ ℤ ℕ Set Matrix Module Complex Real Finset Filter
forall exists and or not iff true false True False Or And Not Iff
deriving where mutual partial unsafe macro syntax notation infixl infixr prefix
all_goals any_goals first repeat try skip focus case next swap
gcongr bound aesop tauto exfalso absurd congr subst symm trans
""".split())


def body_of(text: str) -> str:
    """Return a conservative indentation-based approximation of proof bodies."""
    out: list[str] = []
    inproof = False
    for line in text.split("\n"):
        if re.search(r":=\s*by\s*$|:=\s*by\s", line):
            inproof = True
            out.append(line.split(":=", 1)[-1])
            continue
        if inproof:
            if line.strip() == "" or (line and not line[0].isspace() and not line.startswith("--")):
                if line and not line[0].isspace():
                    inproof = False
                    continue
            out.append(line)
    return "\n".join(out)


def _projection(items: list[dict[str, Any]]) -> list[tuple[Any, ...]]:
    """Return a multiplicity-preserving projection after exact type checks."""
    expected_types = {
        "kind": str,
        "name": str,
        "file": str,
        "line": int,
        "signature": str,
    }
    projection: list[tuple[Any, ...]] = []
    try:
        for index, item in enumerate(items):
            row: list[Any] = []
            for field in PROJECTION_FIELDS:
                value = item[field]
                expected_type = expected_types[field]
                if type(value) is not expected_type:
                    raise AtomIndexError(
                        "malformed declaration projection: "
                        f"item={index} field={field} "
                        f"type={type(value).__name__} expected={expected_type.__name__}"
                    )
                row.append(value)
            projection.append(tuple(row))
    except (KeyError, TypeError) as exc:
        raise AtomIndexError(f"malformed declaration projection: {exc}") from exc
    return sorted(projection)


def validate_inventory(repo: Path, inventory_path: Path) -> tuple[list[Path], list[dict[str, Any]]]:
    """Return complete sources and inventory items after exact live validation."""
    routeb = repo / ROUTEB_REL
    if not routeb.is_dir():
        raise AtomIndexError(f"Route B source directory missing: {routeb}")

    source_files = sorted(
        path for path in routeb.rglob("*.lean")
        if inventory_module.MUSEUM not in path.parts
    )
    if not source_files:
        raise AtomIndexError("Route B source tree is empty")

    try:
        raw_inventory = json.loads(inventory_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise AtomIndexError(f"cannot read declaration inventory: {exc}") from exc
    if not isinstance(raw_inventory, dict) or not isinstance(raw_inventory.get("items"), list):
        raise AtomIndexError("inventory must be an object with an items list")
    if raw_inventory.get("scope") != "RouteB":
        raise AtomIndexError("inventory scope is not RouteB")

    live_items, scanned_files = inventory_module.scan(repo, "RouteB")
    if scanned_files != len(source_files):
        raise AtomIndexError(
            f"source read coverage drift: scanned={scanned_files} source={len(source_files)}"
        )
    inventory_files_scanned = raw_inventory.get("files_scanned")
    if (
        type(inventory_files_scanned) is not int
        or inventory_files_scanned != len(source_files)
    ):
        raise AtomIndexError(
            "inventory file denominator drift: "
            f"inventory={inventory_files_scanned!r} source={len(source_files)}"
        )

    inventory_items = raw_inventory["items"]
    live_projection = _projection(live_items)
    inventory_projection = _projection(inventory_items)
    if live_projection != inventory_projection:
        live_only = sorted(set(live_projection) - set(inventory_projection))[:3]
        inventory_only = sorted(set(inventory_projection) - set(live_projection))[:3]
        raise AtomIndexError(
            "inventory declaration projection drift: "
            f"live_only={live_only!r} inventory_only={inventory_only!r}"
        )
    return source_files, inventory_items


def build_rows(
    repo: Path,
    source_files: list[Path],
    inventory_items: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Build the unchanged bare-list v1 atom rows."""
    routeb = repo / ROUTEB_REL
    own: set[str] = set()
    for item in inventory_items:
        name = item["name"]
        own.add(name)
        own.add(name.split(".")[-1])

    atom_use: dict[str, set[str]] = collections.defaultdict(set)
    total = len(source_files)
    print(f"[инвентарь] своих объектов: {len(own)}", flush=True)
    print(f"[покрытие] RouteB recursive: {total}/{total}", flush=True)
    for index, path in enumerate(source_files, 1):
        if index % 20 == 0 or index == total:
            print(f"[{index}/{total}] {index * 100 // total}% | {path.name}", flush=True)
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            raise AtomIndexError(f"cannot read source file {path}: {exc}") from exc
        file_id = path.relative_to(routeb).as_posix()
        for match in IDENT.finditer(body_of(text)):
            name = match.group(0)
            short = name.split(".")[-1]
            if name in NOISE or short in NOISE:
                continue
            if name in own or short in own:
                continue
            if len(name) < 4 or (name[0].isupper() and "." not in name and short in NOISE):
                continue
            if re.fullmatch(r"h[A-Za-z0-9_']{0,12}", name):
                continue
            if "." not in name and "_" not in name:
                continue
            atom_use[name].add(file_id)

    rows = sorted(atom_use.items(), key=lambda item: (-len(item[1]), item[0]))
    return [
        {"atom": atom, "n_files": len(files), "files": sorted(files)}
        for atom, files in rows
    ]


def atomic_write_json(output: Path, rows: list[dict[str, Any]]) -> None:
    """Publish complete JSON with atomic replacement in the destination directory."""
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=output.parent,
            prefix=f".{output.name}.", suffix=".tmp", delete=False,
        ) as handle:
            temporary = Path(handle.name)
            json.dump(rows, handle, ensure_ascii=False, indent=1)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, output)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def generate(repo: Path, inventory_path: Path, output: Path) -> list[dict[str, Any]]:
    source_files, inventory_items = validate_inventory(repo, inventory_path)
    rows = build_rows(repo, source_files, inventory_items)
    atomic_write_json(output, rows)
    return rows


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", nargs="?", default="atoms.json")
    parser.add_argument("--root", type=Path, default=REPO, help=argparse.SUPPRESS)
    parser.add_argument("--inventory", type=Path, default=DEFAULT_INVENTORY, help=argparse.SUPPRESS)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        rows = generate(args.root.resolve(), args.inventory.resolve(), Path(args.output).resolve())
    except AtomIndexError as exc:
        print(f"ATOM_INDEX_DRIFT: {exc}", file=sys.stderr)
        return 1
    except OSError as exc:
        print(f"ATOM_INDEX_INFRASTRUCTURE_ERROR: {exc}", file=sys.stderr)
        return 2

    print(f"\n[итог] уникальных внешних атомов: {len(rows)}", flush=True)
    print(f"[записано] {Path(args.output).resolve()}", flush=True)
    print("\n=== ТОП-40 самых нагруженных атомов ===", flush=True)
    for row in rows[:40]:
        print(f"{row['n_files']:4d}  {row['atom']}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
