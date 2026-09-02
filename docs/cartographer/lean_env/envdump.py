#!/usr/bin/env python3
"""Собрать индекс Lean environment: имя → ELABORATED тип, аксиомы, адрес.

ЗАЧЕМ. Слой 1 конструктора. `atom_describe.py` читает исходный ТЕКСТ и потому не
видит переменных внешней `section`, неявных параметров, universe-параметров, посылок
typeclass после elaboration, вставленных приведений и раскрытых нотаций. Решать по
тексту о применимости теоремы нельзя. Источник истины — сам Lean.

КАК. Подставляет `import` собранных модулей в `EnvDump.lean` и запускает его через
`lake env lean`. Один прогон на всё дерево: окружение строится один раз.

ЧТО НЕ ДЕЛАЕТ. Не собирает Lean. Видит ТОЛЬКО то, что уже скомпилировано в
`.lake/build`, и говорит вслух, сколько модулей пропустил. Не судит применимость —
это индекс, а не comparator.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN_ROOT = REPO / "q3.lean.aristotle"
BUILD_LIB = LEAN_ROOT / ".lake/build/lib/lean"
TEMPLATE = HERE / "EnvDump.lean"

REQUIRED_RECORD_FIELDS = {
    "name", "kind", "type", "levelParams", "numBinders", "file", "line",
    "doc", "typeConsts", "axioms", "isPrivate", "isUnsafe",
}
EXPECTED_STATE_SCHEMA = "q3_envdump_expected_state.v1"


def built_modules(prefix: str) -> list[str]:
    """Модули с готовым .olean. Только их можно импортировать без пересборки."""
    out = []
    for o in sorted(BUILD_LIB.rglob("*.olean")):
        mod = str(o.relative_to(BUILD_LIB).with_suffix("")).replace("/", ".")
        if mod.startswith(prefix):
            out.append(mod)
    return out


def source_modules(prefix: str) -> list[str]:
    """Модули, у которых есть исходник. Разница с `built_modules` — цена честности:
    индекс покрывает не дерево, а собранную его часть, и это надо печатать."""
    out = []
    base = prefix.split(".")[0]
    for f in sorted((LEAN_ROOT / base).rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        mod = str(f.relative_to(LEAN_ROOT).with_suffix("")).replace("/", ".")
        if mod.startswith(prefix):
            out.append(mod)
    return out


def source_backed_modules(built: list[str], sources: list[str]) \
        -> tuple[list[str], list[str], list[str]]:
    """Отделить текущие модули от сиротских `.olean`.

    Build-кэш переживает удаление исходника. Импортировать такую сироту нельзя:
    она уже не является декларацией текущего дерева и может конфликтовать с её
    канонической заменой. Возвращаем (импортировать, не собрано, сироты).
    """
    bset, sset = set(built), set(sources)
    return sorted(bset & sset), sorted(sset - bset), sorted(bset - sset)


def stale_source_modules(modules: list[str]) -> list[str]:
    """`.olean` старше своего `.lean` не описывает текущее исходное дерево."""
    out = []
    for mod in modules:
        rel = Path(*mod.split("."))
        source = LEAN_ROOT / rel.with_suffix(".lean")
        olean = BUILD_LIB / rel.with_suffix(".olean")
        if source.stat().st_mtime > olean.stat().st_mtime:
            out.append(mod)
    return out


def _validated_records(stdout: str) -> tuple[list[dict], list[str]]:
    """Разобрать JSONL Lean и отвергнуть частичный/неверный индекс."""
    records, diagnostics = [], []
    seen: set[str] = set()
    for line_no, line in enumerate(stdout.splitlines(), 1):
        if not line.startswith("{"):
            if line.strip():
                diagnostics.append(line)
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as exc:
            diagnostics.append(f"stdout:{line_no}: неверный JSON: {exc}")
            continue
        if not isinstance(record, dict):
            diagnostics.append(f"stdout:{line_no}: JSON-запись не объект")
            continue
        missing = REQUIRED_RECORD_FIELDS - record.keys()
        if missing:
            diagnostics.append(
                f"stdout:{line_no}: нет полей {', '.join(sorted(missing))}")
            continue
        type_text = record.get("type")
        if not isinstance(type_text, str) or not type_text:
            diagnostics.append(
                f"stdout:{line_no}: пустой/нестроковый elaborated type")
            continue
        if "⋯" in type_text or "<pp failed>" in type_text:
            diagnostics.append(
                f"stdout:{line_no}: неполный pretty-print типа")
            continue
        name = record.get("name")
        if not isinstance(name, str) or not name:
            diagnostics.append(f"stdout:{line_no}: пустое/нестроковое имя")
            continue
        if name in seen:
            diagnostics.append(f"stdout:{line_no}: дубликат объявления {name}")
            continue
        seen.add(name)
        records.append(record)
    return records, diagnostics


def _write_jsonl_atomic(records: list[dict], out_path: Path) -> None:
    """Опубликовать только целиком проверенный derived-индекс."""
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=out_path.parent,
            prefix=f".{out_path.name}.", suffix=".tmp", delete=False) as f:
        tmp = Path(f.name)
        for record in records:
            f.write(json.dumps(record, ensure_ascii=False, separators=(",", ":")))
            f.write("\n")
    os.replace(tmp, out_path)


def exact_name_set_diagnostics(
    records: list[dict], exact_names: list[str]
) -> tuple[list[str], list[str]]:
    """Return explicit set drift for exact-name mode before publication."""
    requested = set(exact_names)
    returned = {str(record.get("name")) for record in records}
    return sorted(requested - returned), sorted(returned - requested)


def run(mods: list[str], prefixes: list[str], exact_names: list[str],
        timeout: int) -> tuple[int, list[dict], str]:
    src = TEMPLATE.read_text(encoding="utf-8")
    assert "-- IMPORTS_PLACEHOLDER" in src, "в шаблоне нет метки импортов"
    imports = "\n".join(f"import {m}" for m in mods)
    src = src.replace("-- IMPORTS_PLACEHOLDER", imports)
    pref = ", ".join(f"`{p}" for p in prefixes)
    names = ", ".join(f"`{name}" for name in exact_names)
    module_filter = ", ".join(f"`{m}" for m in mods)
    src = src.replace(
        "dumpEnv [] [] []", f"dumpEnv [{pref}] [{names}] [{module_filter}]"
    )

    with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=LEAN_ROOT,
            prefix="EnvDumpRun_", suffix=".lean", delete=False) as f:
        f.write(src)
        run_file = Path(f.name)
    try:
        r = subprocess.run(["lake", "env", "lean", run_file.name],
                           cwd=LEAN_ROOT, capture_output=True, text=True,
                           timeout=timeout)
    finally:
        run_file.unlink(missing_ok=True)

    # Lean шлёт и диагностику, и наш вывод в stdout. Даже если он успел напечатать
    # часть JSON до ошибки, такой индекс не публикуется.
    records, diagnostics = _validated_records(r.stdout)
    if r.stderr.strip():
        diagnostics.append(r.stderr.strip())
    code = r.returncode
    if not records:
        diagnostics.append("ноль объявлений — это отказ, а не пустой результат")
        code = code or 1
    if diagnostics and any("неверный JSON" in x or "нет полей" in x
                           or "дубликат объявления" in x
                           or "не объект" in x or "пустое/нестроковое" in x
                           or "неполный pretty-print типа" in x
                           for x in diagnostics):
        code = code or 1
    return code, records, "\n".join(diagnostics)


def module_selection(prefix: str, limit: int = 0, *, lake_validated: bool = False) \
        -> tuple[list[str], list[str], list[str], list[str], list[str]]:
    """Freeze one honest import selection and all coverage-denominator classes."""
    built_all = built_modules(prefix)
    sources = source_modules(prefix)
    source_backed, never_built, orphaned = source_backed_modules(built_all, sources)
    # Git checkout and cache restoration legitimately make source mtimes newer
    # than byte-current oleans.  A caller that just completed `lake query Q3`
    # has stronger content-addressed evidence than this conservative heuristic.
    stale = [] if lake_validated else stale_source_modules(source_backed)
    selected = sorted(set(source_backed) - set(stale))
    if limit:
        selected = selected[:limit]
    return selected, sources, never_built, orphaned, stale


def module_state_fingerprint(prefix: str) -> tuple[tuple[str, int, int], ...]:
    """Detect a concurrent source/build rewrite even when module names stay equal."""
    rows = []
    source_root = LEAN_ROOT / prefix.split(".")[0]
    for path in sorted(source_root.rglob("*.lean")):
        mod = str(path.relative_to(LEAN_ROOT).with_suffix("")).replace("/", ".")
        if mod.startswith(prefix):
            stat = path.stat()
            rows.append((f"source:{mod}", stat.st_mtime_ns, stat.st_size))
    for path in sorted(BUILD_LIB.rglob("*.olean")):
        mod = str(path.relative_to(BUILD_LIB).with_suffix("")).replace("/", ".")
        if mod.startswith(prefix):
            stat = path.stat()
            rows.append((f"olean:{mod}", stat.st_mtime_ns, stat.st_size))
    return tuple(rows)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def module_content_fingerprint(prefix: str) -> tuple[tuple[str, int, str], ...]:
    """Bind exact source and olean bytes for one Lake-validated read epoch."""
    rows: list[tuple[str, int, str]] = []
    sources = source_modules(prefix)
    built = built_modules(prefix)
    for kind, modules, base, suffix in (
        ("source", sources, LEAN_ROOT, ".lean"),
        ("olean", built, BUILD_LIB, ".olean"),
        # Lake traces bind the content-addressed transitive import closure,
        # compiler identity, options and source digest used for each olean.
        ("trace", built, BUILD_LIB, ".trace"),
    ):
        for module in modules:
            path = base / Path(*module.split(".")).with_suffix(suffix)
            if not path.is_file():
                raise FileNotFoundError(f"нет build identity {path}")
            rows.append((f"{kind}:{module}", path.stat().st_size, _sha256_file(path)))
    return tuple(rows)


def dependency_artifact_roots() -> tuple[tuple[str, Path], ...]:
    lean_prefix = subprocess.run(
        ["lean", "--print-prefix"],
        cwd=LEAN_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if lean_prefix.returncode != 0 or not lean_prefix.stdout.strip():
        raise FileNotFoundError("cannot resolve Lean toolchain prefix")
    toolchain_root = Path(lean_prefix.stdout.strip()) / "lib/lean"
    package_roots = tuple(
        (f"package:{path.parents[3].name}", path)
        for path in sorted((LEAN_ROOT / ".lake/packages").glob("*/.lake/build/lib/lean"))
    )
    return (("project", BUILD_LIB), *package_roots, ("toolchain", toolchain_root))


def dependency_content_digest() -> str:
    """Hash the actual compiled closure EnvDump can load, not only Lake metadata."""
    digest = hashlib.sha256()
    for label, root in dependency_artifact_roots():
        current = Path(root.anchor)
        for component in root.parts[1:]:
            current /= component
            if current.is_symlink():
                raise ValueError(f"symlink dependency root component forbidden: {current}")
        if not root.is_dir():
            raise FileNotFoundError(f"нет dependency artifact root {root}")
        paths: list[Path] = []
        for directory, dirnames, filenames in os.walk(root, followlinks=False):
            base = Path(directory)
            for name in dirnames:
                child = base / name
                if child.is_symlink():
                    raise ValueError(f"symlink dependency directory forbidden: {child}")
            for name in filenames:
                path = base / name
                if path.is_symlink():
                    raise ValueError(f"symlink dependency artifact forbidden: {path}")
                if name.endswith(".trace") or ".olean" in name:
                    paths.append(path)
        paths.sort()
        for path in paths:
            relative = path.relative_to(root).as_posix()
            stat = path.stat()
            digest.update(label.encode("utf-8"))
            digest.update(b"\0")
            digest.update(relative.encode("utf-8"))
            digest.update(b"\0")
            digest.update(str(stat.st_size).encode("ascii"))
            digest.update(b"\0")
            with path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(chunk)
            digest.update(b"\0")
    return digest.hexdigest()


def load_expected_state(
    path: Path, prefix: str
) -> tuple[tuple[tuple[str, int, str], ...], str]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"неверный expected-state: {exc}") from exc
    if not isinstance(value, dict) or set(value) != {
        "schema", "prefix", "entries", "dependency_digest"
    }:
        raise ValueError("неверная схема expected-state")
    if value.get("schema") != EXPECTED_STATE_SCHEMA or value.get("prefix") != prefix:
        raise ValueError("expected-state не совпадает с prefix/schema")
    entries = value.get("entries")
    if not isinstance(entries, list):
        raise ValueError("expected-state entries не являются массивом")
    parsed: list[tuple[str, int, str]] = []
    for row in entries:
        if (
            not isinstance(row, list)
            or len(row) != 3
            or not isinstance(row[0], str)
            or not isinstance(row[1], int)
            or not isinstance(row[2], str)
            or len(row[2]) != 64
        ):
            raise ValueError("неверная строка expected-state")
        parsed.append((row[0], row[1], row[2]))
    dependency_digest = value.get("dependency_digest")
    if not isinstance(dependency_digest, str) or len(dependency_digest) != 64:
        raise ValueError("неверный dependency_digest expected-state")
    return tuple(parsed), dependency_digest


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--prefix", default="Q3.Proofs.RouteB",
                    help="какие модули импортировать (по умолчанию RouteB)")
    ap.add_argument("--namespace", action="append", default=None,
                    help="опциональный повторяемый фильтр имён; по умолчанию все выбранные модули")
    ap.add_argument("--name", action="append", default=None,
                    help="опциональное точное имя декларации; повторяемый")
    ap.add_argument("--module", action="append", default=None,
                    help="опциональный точный source-backed модуль; повторяемый")
    ap.add_argument("--out", default=str(HERE / "env_index.jsonl"))
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--limit", type=int, default=0, help="взять первые N модулей")
    ap.add_argument(
        "--expected-state",
        type=Path,
        help="exact content snapshot, созданный сразу после lake query Q3",
    )
    a = ap.parse_args()

    if not BUILD_LIB.is_dir():
        print(f"нет каталога сборки {BUILD_LIB} — сначала lake build", file=sys.stderr)
        return 2

    try:
        expected_state = (
            load_expected_state(a.expected_state, a.prefix)
            if a.expected_state is not None
            else None
        )
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 2
    if expected_state is not None:
        expected_modules, expected_dependencies = expected_state
        if (
            module_content_fingerprint(a.prefix) != expected_modules
            or dependency_content_digest() != expected_dependencies
        ):
            print("expected-state изменился до EnvDump", file=sys.stderr)
            return 2

    selected_all, have_src, missing_modules, orphaned_oleans, stale_oleans = \
        module_selection(a.prefix, a.limit, lake_validated=expected_state is not None)
    selection_before = (
        selected_all, have_src, missing_modules, orphaned_oleans, stale_oleans
    )
    built = selected_all
    if a.module:
        requested_modules = sorted(set(a.module))
        unavailable = sorted(set(requested_modules) - set(built))
        if unavailable:
            print(
                "requested modules unavailable: " + ", ".join(unavailable),
                file=sys.stderr,
            )
            return 2
        built = requested_modules
    before_state = module_state_fingerprint(a.prefix)
    if not built:
        print(f"под префиксом {a.prefix} нет ни одного собранного модуля", file=sys.stderr)
        return 2

    # ЗНАМЕНАТЕЛЬ ПОКРЫТИЯ. Зелёный отчёт по трети дерева читается как зелёный по
    # всему дереву. Печатаем обе величины ВСЕГДА, а не только когда всё сошлось.
    print(f"модулей с исходником       : {len(have_src)}")
    print(f"актуальных собранных       : {len(built)}")
    print(f"устаревших .olean исключено: {len(stale_oleans)}")
    for mod in stale_oleans[:10]:
        print(f"   устарел: {mod}")
    print(f"сиротских .olean исключено : {len(orphaned_oleans)}")
    for mod in orphaned_oleans[:10]:
        print(f"   сирота: {mod}")
    missing = len(have_src) - len(built)
    if missing > 0:
        print(f"НЕ ПОКРЫТО                 : {missing} — их объявлений в индексе НЕТ")
    if a.limit:
        print(f"лимит импорта              : {a.limit}")

    code, records, errs = run(
        built, a.namespace or [], sorted(set(a.name or [])), a.timeout
    )
    if a.name:
        missing_names, unexpected_names = exact_name_set_diagnostics(
            records, sorted(set(a.name))
        )
        if missing_names or unexpected_names:
            if missing_names:
                print(
                    "requested exact names missing: " + ", ".join(missing_names),
                    file=sys.stderr,
                )
            if unexpected_names:
                print(
                    "unexpected exact names returned: " + ", ".join(unexpected_names),
                    file=sys.stderr,
                )
            print("индекс не опубликован: exact --name set mismatch", file=sys.stderr)
            return 1
    n = len(records)
    if errs.strip():
        print("── диагностика Lean ──", file=sys.stderr)
        print(errs[:4000], file=sys.stderr)
    print(f"объявлений в индексе : {n}")
    print(f"файл                 : {a.out}")

    if code != 0:
        print("индекс не опубликован: Lean/JSON прогон не завершился чисто", file=sys.stderr)
        return code

    # Другая сессия могла собрать/удалить модуль во время долгого обхода. В этом
    # случае результат уже устарел до публикации: оставляем прежний индекс целым.
    after = module_selection(a.prefix, a.limit, lake_validated=expected_state is not None)
    if (after != selection_before
            or module_state_fingerprint(a.prefix) != before_state
            or (expected_state is not None
                and (
                    module_content_fingerprint(a.prefix) != expected_state[0]
                    or dependency_content_digest() != expected_state[1]
                ))):
        print("индекс не опубликован: набор .lean/.olean изменился во время прогона",
              file=sys.stderr)
        return 1
    _write_jsonl_atomic(records, Path(a.out))

    # сводка: на чём стоят доказательства
    std = {"propext", "Classical.choice", "Quot.sound"}
    dirty, sorried = [], []
    for d in records:
        extra = set(d["axioms"]) - std
        if "sorryAx" in extra:
            sorried.append(d["name"])
        elif extra:
            dirty.append((d["name"], sorted(extra)))
    print(f"на sorryAx           : {len(sorried)}")
    print(f"на прочих аксиомах   : {len(dirty)}")
    for nm in sorried[:10]:
        print(f"   sorry: {nm}")
    for nm, ax in dirty[:10]:
        print(f"   аксиомы: {nm} ← {', '.join(ax)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
