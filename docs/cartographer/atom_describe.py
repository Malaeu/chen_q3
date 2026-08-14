#!/usr/bin/env python3
"""Обогатить атомы описаниями: что каждый атом ЕСТЬ, а не только как он называется.

Шаг 1 конструктора (замысел владельца 2026-08-11): «декомпозировать Lean полностью до
атомов с описанием, что этот атом из себя представляет — с полным описанием».

Без описания атом — это строка. Строку нельзя ни сопоставить с чужой леммой, ни отдать
агенту как задание: `mul_nonneg` и `posIndexAbove` выглядят одинаково безлико. С сигнатурой
и докстрингом атом становится утверждением, о котором можно рассуждать.

Источники, в порядке приоритета:

  1. Lean environment   `lean_env/env_index.jsonl` — elaborated типы наших деклараций
  2. Mathlib на диске   `q3.lean.aristotle/.lake/packages/mathlib/Mathlib` (100 МБ)
  3. наше дерево        `q3.lean.aristotle/Q3` — адрес и исходный текст
  4. чужое дерево       `--foreign` — их декларации, если атом определён у них

Для каждого атома извлекается: где объявлен (`file:line`), вид (`theorem`/`def`/…),
сигнатура до `:=`, докстринг `/-- … -/` над объявлением, и число мест употребления у нас.

Атомы, которые нигде не нашлись, помечаются `UNRESOLVED` — это либо тактики, либо
нотация, либо имя, разобранное неверно. Их список — самостоятельный результат: он
показывает, где наш разбор до атомов ещё дырявый.

ЧТО ЭТО НЕ ДЕЛАЕТ. Не решает, применим ли атом: докстринг — это пересказ автора, а не
проверка. Правило про суррогат по форме действует.

Read-only: пишет только в `--json`, если указан.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sqlite3
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
DB = f"file:{REPO}/q3.lean.aristotle/aristotle_db/knowledge.db?mode=ro"
MATHLIB = REPO / "q3.lean.aristotle/.lake/packages/mathlib/Mathlib"
OURS = REPO / "q3.lean.aristotle/Q3"

KINDS = "theorem|lemma|def|structure|abbrev|instance|class|inductive"
BASES_YAML = REPO / "docs/cartographer/lean_bases.yaml"
ENV_INDEX = REPO / "docs/cartographer/lean_env/env_index.jsonl"
ENV_REQUIRED_FIELDS = {
    "name", "kind", "type", "levelParams", "numBinders", "file", "line",
    "doc", "typeConsts", "axioms", "isPrivate", "isUnsafe",
}


class EnvIndexError(ValueError):
    """Derived environment index is absent, malformed, ambiguous, or stale."""


def load_env_index(path: Path) -> dict[str, dict]:
    """Read the derived JSONL strictly; a partial index is not a fallback source."""
    if not path.is_file():
        raise EnvIndexError(
            f"нет {path}; сначала python3 docs/cartographer/lean_env/envdump.py")
    out: dict[str, dict] = {}
    for line_no, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip():
            continue
        try:
            rec = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise EnvIndexError(f"{path}:{line_no}: неверный JSON: {exc}") from exc
        if not isinstance(rec, dict):
            raise EnvIndexError(f"{path}:{line_no}: запись не JSON-объект")
        missing = ENV_REQUIRED_FIELDS - rec.keys()
        if missing:
            raise EnvIndexError(
                f"{path}:{line_no}: нет полей {', '.join(sorted(missing))}")
        name = rec.get("name")
        if not isinstance(name, str) or not name:
            raise EnvIndexError(f"{path}:{line_no}: пустое/нестроковое имя")
        if name in out:
            raise EnvIndexError(f"{path}:{line_no}: дубликат объявления {name}")
        type_text = rec.get("type")
        if not isinstance(type_text, str) or not type_text:
            raise EnvIndexError(f"{path}:{line_no}: type у {name} не строка")
        if "⋯" in type_text or "<pp failed>" in type_text:
            raise EnvIndexError(
                f"{path}:{line_no}: неполный pretty-print типа у {name}")
        for field in ("levelParams", "typeConsts", "axioms"):
            if not isinstance(rec.get(field), list):
                raise EnvIndexError(f"{path}:{line_no}: {field} у {name} не список")
        out[name] = rec
    if not out:
        raise EnvIndexError(f"{path}: ноль объявлений")
    return out


def declaration_full_name(requested: str, source: dict) -> str:
    """Reconstruct the exact environment name from a source declaration."""
    if requested.startswith("Q3."):
        return requested
    namespace = source.get("namespace", "")
    if "." in requested:
        return ".".join(x for x in (namespace, requested) if x)
    if source.get("kind_lean") == "field":
        owner = source.get("owner", "")
        return ".".join(x for x in (namespace, owner, requested) if x)
    return ".".join(x for x in (namespace, requested) if x)


def source_module_name(source: dict) -> str:
    """Turn the tracked Lean path into the module identity stored by Lean."""
    path = source.get("file", "")
    prefix = "q3.lean.aristotle/"
    if not path.startswith(prefix) or not path.endswith(".lean"):
        raise EnvIndexError(f"неожиданный адрес нашей декларации: {path}")
    return path[len(prefix):-len(".lean")].replace("/", ".")


def enrich_from_env(requested: str, source: dict, env_index: dict[str, dict],
                    index_mtime: float) -> dict:
    """Replace a RouteB source-text signature by its exact elaborated environment type."""
    full_name = declaration_full_name(requested, source)
    env = env_index.get(full_name)
    if env is None:
        raise EnvIndexError(f"{full_name}: нет в env_index (модуль не собран или индекс устарел)")
    expected_module = source_module_name(source)
    if env.get("file") != expected_module:
        raise EnvIndexError(
            f"{full_name}: env module {env.get('file')!r} != source {expected_module!r}")
    source_path = REPO / source["file"]
    if source_path.is_file() and source_path.stat().st_mtime > index_mtime:
        raise EnvIndexError(f"{full_name}: исходник новее env_index; нужен envdump rerun")

    out = dict(source)
    out["source_signature"] = out.pop("signature", "")
    out["source_kind_lean"] = out.get("kind_lean", "")
    out["description_source"] = "LEAN_ENV"
    out["elaborated_name"] = full_name
    out["elaborated_type"] = env["type"]
    out["signature"] = f"{full_name} : {env['type']}"
    out["kind_lean"] = env["kind"]
    out["levelParams"] = env["levelParams"]
    out["numBinders"] = env["numBinders"]
    out["typeConsts"] = env["typeConsts"]
    out["axioms"] = env["axioms"]
    out["isPrivate"] = env["isPrivate"]
    out["isUnsafe"] = env["isUnsafe"]
    if env.get("doc"):
        out["docstring"] = env["doc"]
    return out


def write_json_atomic(path: Path, value: object) -> None:
    """Do not leave a plausible partial derived result."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", dir=path.parent,
            prefix=f".{path.name}.", suffix=".tmp", delete=False) as f:
        tmp = Path(f.name)
        json.dump(value, f, indent=2, ensure_ascii=False)
        f.write("\n")
    os.replace(tmp, path)


def _base_identity(p: Path) -> dict:
    """Прочитать, ЧТО именно лежит по пути: origin, HEAD, чистота, toolchain."""
    def git(*a):
        try:
            r = subprocess.run(["git", "-C", str(p), *a], capture_output=True,
                               text=True, timeout=30)
            return r.stdout.strip() if r.returncode == 0 else None
        except Exception:
            return None
    tc = p / "lean-toolchain"
    return {
        "origin": git("remote", "get-url", "origin"),
        "head": (git("rev-parse", "--short", "HEAD") or ""),
        "dirty": bool((git("status", "--porcelain") or "").strip()),
        "toolchain": tc.read_text(encoding="utf-8").strip() if tc.is_file() else None,
    }


def enabled_base_ids(path: Path = BASES_YAML) -> list[str]:
    """Return the closed enabled-base denominator from the registry.

    Callers making absence claims must compare this list with the bases they
    actually queried.  ``load_bases`` alone cannot provide that denominator:
    an unresolved or ambiguous enabled base is deliberately omitted there.
    """
    if not path.is_file():
        raise EnvIndexError(f"нет реестра внешних Lean-баз: {path}")
    try:
        import yaml
    except ImportError as exc:
        raise EnvIndexError(f"реестр внешних Lean-баз не прочитан: {exc}") from exc
    try:
        registry = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except (OSError, UnicodeDecodeError, yaml.YAMLError) as exc:
        raise EnvIndexError(f"реестр внешних Lean-баз не прочитан: {exc}") from exc
    if registry.get("schema") != "q3_lean_bases.v1":
        raise EnvIndexError("неподдерживаемая schema реестра внешних Lean-баз")
    bases = registry.get("bases")
    if not isinstance(bases, list):
        raise EnvIndexError("поле bases реестра не является списком")
    enabled: list[str] = []
    for index, row in enumerate(bases):
        if not isinstance(row, dict):
            raise EnvIndexError(f"bases[{index}] не является объектом")
        if not row.get("enabled"):
            continue
        base_id = row.get("id")
        if not isinstance(base_id, str) or not base_id.strip():
            raise EnvIndexError(f"bases[{index}] имеет пустой id")
        if base_id in enabled:
            raise EnvIndexError(f"дубликат enabled base id: {base_id}")
        enabled.append(base_id)
    return enabled


def load_bases(explicit: str = "", strict: bool = True) -> list[tuple[str, Path]]:
    """Прочитать реестр внешних Lean-баз и разрешить путь для ЭТОЙ машины.

    HIGH-6, ревью Codex 2026-08-12. Прежняя версия брала первый путь, у которого
    `is_dir()` истинно. Существование каталога ничего не говорит о его содержимом:
    это мог быть старый клон, другой origin или другой toolchain, а второй кандидат
    молча игнорировался. На втором теле такая база ищет не там и не жалуется.

    Теперь у каждого кандидата читаются origin, HEAD, чистота и toolchain, и они
    сверяются с записью реестра. Кандидат с чужим origin отвергается. Расхождение
    HEAD или toolchain печатается, но базу не отключает: она обновилась, а не
    подменилась. Два кандидата с разными HEAD — отказ, потому что выбрать нельзя.

    `explicit` (`--foreign`) не отменяет реестр, а добавляется к нему. MEDIUM-13:
    несуществующий явный путь больше не проходит молча.
    """
    out: list[tuple[str, Path]] = []
    if explicit:
        p = Path(explicit).expanduser().resolve()
        if not p.is_dir():
            print(f"  --foreign {p}: каталога нет", file=sys.stderr)
        elif not any(p.rglob("*.lean")):
            print(f"  --foreign {p}: каталог есть, файлов .lean нет", file=sys.stderr)
        else:
            out.append(("--foreign", p))
    if not BASES_YAML.is_file():
        return out
    try:
        import yaml
    except ImportError:
        print("  реестр баз не прочитан: нет PyYAML "
              "(pip install pyyaml / uv add pyyaml)", file=sys.stderr)
        return out
    try:
        reg = yaml.safe_load(BASES_YAML.read_text(encoding="utf-8")) or {}
    except Exception as e:
        print(f"  реестр баз не прочитан: {e}", file=sys.stderr)
        return out

    for b in reg.get("bases", []):
        if not b.get("enabled"):
            continue
        bid = b["id"]
        found = []
        for cand in b.get("paths", []):
            p = Path(cand).expanduser()
            if p.is_dir():
                found.append((p, _base_identity(p)))
        if not found:
            print(f"  база {bid}: НЕ НАЙДЕНА ни по одному пути — "
                  f"подтяните {b.get('origin','?')}", file=sys.stderr)
            continue

        want_origin = (b.get("origin") or "").removesuffix(".git")
        ok = []
        for p, ident in found:
            got = (ident["origin"] or "").removesuffix(".git")
            if want_origin and got and got != want_origin:
                print(f"  база {bid}: путь {p} — ЧУЖОЙ origin {got}, отвергнут",
                      file=sys.stderr)
                continue
            ok.append((p, ident))
        if not ok:
            print(f"  база {bid}: ни один путь не совпал по origin", file=sys.stderr)
            continue
        if len({i["head"] for _, i in ok}) > 1 and strict:
            heads = ", ".join(f"{p}={i['head']}" for p, i in ok)
            print(f"  база {bid}: НЕСКОЛЬКО КЛОНОВ С РАЗНЫМИ HEAD ({heads}) — "
                  f"выбрать нельзя, база отключена", file=sys.stderr)
            continue

        p, ident = ok[0]
        pin = b.get("pin") or {}
        if pin.get("head") and ident["head"] and pin["head"] != ident["head"]:
            print(f"  база {bid}: HEAD {ident['head']} против записанного "
                  f"{pin['head']} — адреса из verified_by могли сдвинуться",
                  file=sys.stderr)
        if b.get("toolchain") and ident["toolchain"] and b["toolchain"] != ident["toolchain"]:
            print(f"  база {bid}: toolchain {ident['toolchain']} против записанного "
                  f"{b['toolchain']}", file=sys.stderr)
        if ident["dirty"] and not pin.get("checked_clean", True):
            pass                                  # грязь уже зафиксирована в реестре
        elif ident["dirty"]:
            print(f"  база {bid}: рабочее дерево грязное — содержимое не равно {ident['head']}",
                  file=sys.stderr)
        out.append((bid, p))
    return out


def namespace_at(lines: list[str], line: int) -> str:
    """Восстановить namespace-стек над строкой: `namespace A` … `end A`, плюс `open`-независимо."""
    stack = []
    for k in range(line - 1):
        s = lines[k].strip()
        m = re.match(r"^namespace\s+([A-Za-z_][A-Za-z_0-9'\.]*)", s)
        if m:
            stack.extend(m.group(1).split("."))
            continue
        m = re.match(r"^end\s+([A-Za-z_][A-Za-z_0-9'\.]*)", s)
        if m and stack:
            for part in reversed(m.group(1).split(".")):
                if stack and stack[-1] == part:
                    stack.pop()
    return ".".join(stack)


def find_structure_field(name: str, root: Path) -> dict | None:
    """Найти имя как ПОЛЕ СТРУКТУРЫ: строка `  name : тип` внутри `structure X where`.

    ДЕФЕКТ 2026-08-12 (а): поиск объявлений ищет только `theorem|def|…`, поэтому
    `kTrial` — поле `CoefficientFamily` — возвращался как `PLACEHOLDER`, то есть «ещё
    не написан», для объекта, который в дереве с самого начала.

    ДЕФЕКТ 2026-08-12 (б), HIGH-5 ревью Codex: первая починка поднималась вверх и
    обрывалась на строке «непустая, не комментарий, без двоеточия». Продолжение
    многострочного типа предыдущего поля выглядит ровно так, и подъём не доходил до
    заголовка. Терялись `lambda_eq`, `eStar_memLp`, `trialNonzero`, `outerBlock`,
    `outerBlock_positive`. Лимит в 40 строк терял поля дальше по структуре.

    Теперь признак владельца — КОЛОНКА НОЛЬ: поле лежит с отступом, а объявление
    структуры начинается без отступа. Между ними не должно быть другой строки с
    нулевым отступом. Ни двоеточия, ни лимита строк это правило не требует.
    """
    if not root.is_dir() or "." in name:
        return None
    try:
        r = subprocess.run(
            ["rg", "-n", "--no-heading", rf"^\s+{re.escape(name)}\s*:", str(root)],
            capture_output=True, text=True, timeout=180)
    except Exception:
        return None
    if r.returncode != 0 or not r.stdout.strip():
        return None
    for c in r.stdout.strip().split("\n")[:200]:
        try:
            path_s, line_s, body = c.split(":", 2)
            cp, cl = Path(path_s), int(line_s)
            lines = cp.read_text(encoding="utf-8", errors="replace").split("\n")
        except Exception:
            continue
        owner = None
        for k in range(cl - 2, -1, -1):
            ln = lines[k]
            if not ln.strip():
                continue
            if ln[0].isspace():
                continue                       # ещё внутри блока
            m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*"
                         r"(structure|class)\s+([A-Za-z_][A-Za-z_0-9'\.]*)", ln)
            owner = m.group(2) if m else None
            break                              # первая строка колонки ноль решает
        if owner is None:
            continue
        return {
            "kind_lean": "field",
            "namespace": namespace_at(lines, cl),
            "owner": owner,
            "file": str(cp.relative_to(REPO)) if str(cp).startswith(str(REPO)) else str(cp),
            "line": cl,
            "signature": f"{owner}.{name} : " + body.split(":", 1)[1].strip()[:200],
            "docstring": "",
        }
    return None


def find_declaration(name: str, root: Path) -> dict | None:
    """Найти объявление ТОЧНО этого полного имени: базовое имя плюс совпадающий namespace.

    ПОПРАВКА 2026-08-11: первая версия искала по базовому имени с `-m 1` и брала первое
    попавшееся. Так `Real.pi` находился как `def pi` из `ContinuousMap` (произведение
    непрерывных отображений), а `Complex.exp` — как степенной ряд из `PowerSeries`.
    Инструмент, дающий правдоподобно неверный ответ, хуже отсутствующего: теперь для
    каждого кандидата восстанавливается namespace-стек и полное имя сверяется с искомым.
    """
    if not root.is_dir():
        return None
    base = name.split(".")[-1]
    want_ns = ".".join(name.split(".")[:-1])
    pat = rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*({KINDS})\s+{re.escape(base)}\b"
    try:
        r = subprocess.run(["rg", "-n", "--no-heading", pat, str(root)],
                           capture_output=True, text=True, timeout=180)
    except Exception:
        return None
    if r.returncode != 0 or not r.stdout.strip():
        return None

    cands = r.stdout.strip().split("\n")[:400]
    path = line = lines = None
    for c in cands:
        try:
            path_s, line_s, _ = c.split(":", 2)
            cp, cl = Path(path_s), int(line_s)
            cls = cp.read_text(encoding="utf-8", errors="replace").split("\n")
        except Exception:
            continue
        ns = namespace_at(cls, cl)
        # объявление могло быть записано и полным именем: `theorem Real.pi ...`
        full_written = re.search(rf"({KINDS})\s+{re.escape(name)}\b", cls[cl - 1]) is not None
        if ns == want_ns or full_written or (not want_ns and not ns):
            path, line, lines = cp, cl, cls
            break
    if path is None:
        return None

    # сигнатура: от объявления до `:=` или `by`, максимум 25 строк
    sig, i = [], line - 1
    while i < min(line - 1 + 25, len(lines)):
        sig.append(lines[i].strip())
        if ":=" in lines[i] or re.search(r"\bby\b\s*$", lines[i]):
            break
        i += 1
    signature = " ".join(sig)
    cut = signature.find(":=")
    signature = (signature[:cut] if cut > 0 else signature).strip()

    # докстринг: блок /-- … -/ непосредственно над объявлением
    doc, j = [], line - 2
    if j >= 0 and lines[j].strip().endswith("-/"):
        while j >= 0:
            doc.insert(0, lines[j].strip())
            if lines[j].strip().startswith("/--"):
                break
            j -= 1
    docstring = " ".join(doc).replace("/--", "").replace("-/", "").strip()

    m = re.match(rf"\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*({KINDS})",
                 lines[line - 1])
    return {
        "kind_lean": m.group(1) if m else "?",
        "namespace": namespace_at(lines, line),
        "file": str(path.relative_to(REPO)) if str(path).startswith(str(REPO)) else str(path),
        "line": line,
        "signature": signature[:600],
        "docstring": docstring[:800],
    }


CYR = re.compile(r"[А-Яа-яЁё]")
PAPER = re.compile(r"(Lemma|Theorem|Prop|Proposition)[_ ]?\d", re.I)


_BINDER_CACHE: set[str] | None = None


def _strip_comments(text: str) -> str:
    """Убрать блочные и строчные комментарии Lean.

    MEDIUM-10. Первая попытка чинилась случайностью: двоеточие внутри `-- note:`
    обрывало разбор. Комментарий без двоеточия — `-- see (ghost : Nat)` — протекал,
    и блочный `/- (spook : Nat) -/` тоже. Комментарии удаляются явно.
    """
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    # Построчно: если сначала склеить строки, `--` съест остаток сигнатуры вместе
    # со следующими биндерами. Поймано на себе при починке 2026-08-12.
    return "\n".join(re.sub(r"--.*$", " ", ln) for ln in text.split("\n"))


def _telescope_binders(sig: str) -> list[str]:
    """Вернуть имена, СВЯЗАННЫЕ телескопом объявления, и только их.

    Разбор идёт по символам с учётом глубины скобок. Группа биндеров — та, что
    открывается на верхнем уровне ДО двоеточия заключения. Всё, что глубже или
    после этого двоеточия, телескопом не связано.

    HIGH-3 и MEDIUM-10, поймано ревью Codex 2026-08-12. Прежняя проверка искала
    regex по всему тексту файла и не отличала связывание `(x : T)` от приведения
    типа `(ccmModeFinite N i : ℝ)`, а также ловила имена из комментариев.
    """
    sig = _strip_comments(sig)
    names: list[str] = []
    depth = 0
    group_start = -1
    i = 0
    while i < len(sig):
        c = sig[i]
        if c in "({[":
            depth += 1
            if depth == 1:
                group_start = i + 1
        elif c in ")}]":
            if depth == 1 and group_start >= 0:
                body = sig[group_start:i]
                if ":" in body:
                    head = body.split(":", 1)[0]
                    # инстанс-биндер `[Fintype n]` имён не вводит: двоеточия нет,
                    # сюда не попадёт; `[inst : C]` вводит `inst`.
                    names.extend(w for w in head.split() if re.fullmatch(r"[A-Za-z_][\w'!?]*", w))
                group_start = -1
            depth -= 1
        elif c == ":" and depth == 0:
            break                      # двоеточие заключения: телескоп кончился
        i += 1
    return names


def binder_names() -> set[str]:
    """Все имена, связанные телескопами объявлений дерева RouteB. Один проход, кэш."""
    global _BINDER_CACHE
    if _BINDER_CACHE is not None:
        return _BINDER_CACHE
    out: set[str] = set()
    root = OURS / "Proofs/RouteB"
    for f in root.rglob("*.lean"):
        try:
            lines = f.read_text(encoding="utf-8", errors="replace").split("\n")
        except Exception:
            continue
        i = 0
        while i < len(lines):
            m = re.match(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                         rf"(?:{KINDS})\s+([A-Za-z_][\w'!?.]*)", lines[i])
            if m:
                sig, j = [], i
                while j < min(i + 30, len(lines)):
                    ln = lines[j]
                    sig.append(ln)
                    if ":=" in ln or re.search(r"\bby\b\s*$", ln):
                        break
                    j += 1
                text = " ".join(_strip_comments(ln) for ln in sig)
                text = text[text.index(m.group(1)) + len(m.group(1)):]
                out.update(_telescope_binders(text))
                i = j
            i += 1
    _BINDER_CACHE = out
    return out


def is_local_binder(name: str) -> bool:
    """Связано ли имя телескопом какого-либо объявления RouteB."""
    if "." in name:
        return False
    return name in binder_names()


def resolve_all(name: str, roots: list) -> list[tuple[str, dict]]:
    """Собрать ВСЕХ кандидатов по всем корням, не останавливаясь на первом.

    HIGH, поймано ревью Codex 2026-08-12. Прежний цикл прерывался на первом
    попадании, а Mathlib стоит в списке раньше нашего дерева. Из-за этого правило
    «объявлено в RouteB — значит декларация» не исполнялось никогда: контрпример `H`
    имеет `def H` в `MuntzV3/Core.lean:37`, но поиск отдавал Mathlib и класс выходил
    `LOCAL_HYPOTHESIS`.
    """
    out = []
    for src, root in roots:
        d = find_declaration(name, root) or find_structure_field(name, root)
        if d:
            out.append((src, d))
    return out


def pick_candidate(cands: list[tuple[str, dict]]) -> tuple[str, dict] | None:
    """Выбрать кандидата: наше дерево RouteB важнее Mathlib и внешних баз."""
    for c in cands:
        if "Proofs/RouteB" in c[1].get("file", ""):
            return c
    return cands[0] if cands else None


def provenance(name: str, cands: list[tuple[str, dict]]) -> str:
    """Классифицировать имя по таксономии вердикта `..._HERMFACT1_AUDIT_2026-08-11`.

    ПОРЯДОК ПРОВЕРОК.

    1. Проза — кириллица или пробел: пометка в записи, а не имя объекта.
    2. Объявлено в нашем RouteB **и** связано там же как переменная — `AMBIGUOUS`.
       Адрес не выдаётся: выбрать одно из двух по имени невозможно, а угадать —
       значит вернуться к тому, ради чего эта классификация написана.
    3. Объявлено в нашем RouteB — декларация.
    4. Связано в сигнатурах RouteB — локальная гипотеза с однофамильцем.
    5. Разрешилось где-то ещё — декларация.
    6. Похоже на ссылку из статьи — теорема первоисточника.
    7. Иначе заглушка.

    ТРИ ПРЕЖНИЕ РЕДАКЦИИ БЫЛИ НЕВЕРНЫ, все три в самопроверке.
    Первая ставила разрешение выше связанности и подпирала это порогами длины имени.
    Вторая ставила связанность выше всего — `ccmModeFinite` стал «локальным», потому что
    биндер-паттерн не отличает связывание от приведения типа.
    Третья опиралась на «первое попадание» и до нашего дерева не доходила.
    """
    if CYR.search(name) or " " in name:
        return "PROSE"
    in_routeb = any("Proofs/RouteB" in d.get("file", "") for _, d in cands)
    bound = is_local_binder(name)
    if in_routeb and bound:
        return "AMBIGUOUS"
    if in_routeb:
        return "LEAN_DECL"
    if bound:
        return "LOCAL_HYPOTHESIS"
    if cands:
        return "LEAN_DECL"
    if PAPER.search(name):
        return "PAPER_THEOREM"
    return "PLACEHOLDER"


SELFTEST = [
    # имя,                                        ожидаемый класс,     почему
    ("epsilon",                    "LOCAL_HYPOTHESIS", "связан в сигнатурах, однофамилец в ординалах Веблена"),
    ("xi",                         "LOCAL_HYPOTHESIS", "связан в сигнатурах, однофамилец в RKHS_rescaling"),
    ("hbottom",                    "LOCAL_HYPOTHESIS", "связан, деклараций нет"),
    ("kTrial",                     "LEAN_DECL",        "ПОЛЕ структуры CoefficientFamily, не theorem/def"),
    ("proposition59RawTransform",  "LEAN_DECL",        "имя содержит 'proposition', но это декларация"),
    ("dslope",                     "LEAN_DECL",        "декларация Mathlib, нигде не связана"),
    ("ZerosRealOn",                "LEAN_DECL",        "наша декларация"),
    ("ccmModeFinite",              "LEAN_DECL",        "объявлена в RouteB; биндер-паттерн ловил ПРИВЕДЕНИЕ (ccmModeFinite N i : ℝ)"),
    ("sourceLagrangePolynomial",   "LEAN_DECL",        "объявлена в RouteB"),
    ("centeredPstarFamily",        "LEAN_DECL",        "объявлена в RouteB"),
    ("CCM_Lemma_7_3",              "PAPER_THEOREM",    "в дереве отсутствует, вид ссылки на статью"),
    ("hermfact1",                  "PLACEHOLDER",      "исторический doc-alias: ноль .lean во всём репозитории"),
    ("FiniteGroundTransformToCCMTrialLocallyUniform", "PLACEHOLDER", "ещё не написана"),
    ("кофинальное расписание",     "PROSE",            "пометка, не имя"),
    ("rank_trace_ineq",            "LEAN_DECL",        "ЧУЖАЯ база zeta23: несущее неравенство ранг-след"),
    ("finrank_le_posIndex_of_posDefOn", "LEAN_DECL",   "ЧУЖАЯ база zeta23: устройство «предъяви подпространство»"),
    ("H",                          "AMBIGUOUS",        "def H в MuntzV3/Core.lean:37 И биндер {H T : Type*}; Mathlib находится раньше"),
    ("measure_singleton",          "LEAN_DECL",        "HIGH-3: встречается как приведение (measure_singleton s : volume …)"),
    ("lambda_eq",                  "LEAN_DECL",        "HIGH-5: поле после многострочного типа предыдущего поля"),
    ("outerBlock_positive",        "LEAN_DECL",        "HIGH-5: поле дальше 40-й строки структуры"),
]


def selftest(bases: list) -> int:
    """Прогнать классификатор на именах с ИЗВЕСТНЫМ ответом.

    Инструмент, который нельзя проверить, нельзя и починить: до этой проверки обе
    правки классификатора вносились вслепую и обе оказались с собственными ошибками.
    """
    print("САМОПРОВЕРКА классификатора — 11 имён с известным ответом")
    print()
    bad = 0
    for name, want, why in SELFTEST:
        cands = resolve_all(name, [("mathlib", MATHLIB), ("ours", OURS)] + list(bases))
        found = pick_candidate(cands)
        got = provenance(name, cands)
        ok = got == want
        bad += not ok
        mark = "OK " if ok else "ПРОВАЛ"
        print(f"  {mark} {name[:46]:<46} {got:<17} {why}")
        if not ok:
            print(f"       ожидалось {want}"
                  + (f", адрес {found[1]['file']}:{found[1]['line']}" if found else ", адреса нет"))
    print()
    print(f"провалов: {bad} из {len(SELFTEST)}")
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=0, help="сколько атомов обработать (0 = все)")
    ap.add_argument("--kinds", default="",
                    help="только эти наши kind через запятую, напр. NONVANISHING,ANALYSIS,LINALG")
    ap.add_argument("--foreign", default="", help="корень чужого дерева, третий источник")
    ap.add_argument("--chain", default="",
                    help="разобрать объекты цепи из assembly, а не атомы Mathlib "
                         "(например REALZERO_GROUND_DIAGONAL_TO_XI)")
    ap.add_argument("--json", default="")
    ap.add_argument("--env-index", default=str(ENV_INDEX),
                    help="derived JSONL из lean_env/envdump.py; для RouteB обязателен")
    ap.add_argument("--bases", action="store_true",
                    help="показать реестр внешних Lean-баз и их доступность здесь")
    ap.add_argument("--selftest", action="store_true",
                    help="прогнать классификатор на именах с известным ответом и выйти")
    args = ap.parse_args()

    bases = load_bases(args.foreign)

    if args.bases:
        print("внешние Lean-базы, доступные на этой машине:")
        for bid, p in bases:
            n = len(list(p.rglob("*.lean")))
            print(f"  {bid:<12} {n:>5} .lean  {p}")
        if not bases:
            print("  ни одной — реестр docs/cartographer/lean_bases.yaml")
        if not args.selftest:
            return 0

    if args.selftest:
        return selftest(bases)

    con = sqlite3.connect(DB, uri=True)
    if args.chain:
        # Объекты маршрута — НЕ атомы Mathlib: это наши декларации и имена ещё не
        # написанных теорем. Разбор тот же (где объявлено, сигнатура, докстринг), но
        # `kind` здесь означает шаг цепи, а `n_files` теряет смысл и ставится в 0.
        rows = con.execute(
            "select step, objects, supplier_file from assembly where chain=? order by step",
            (args.chain,)).fetchall()
        seen, atoms = set(), []
        for step, objs, sup in rows:
            for o in (objs or "").split(","):
                o = o.strip()
                if not o or o in seen or "=" in o:
                    continue
                seen.add(o)
                atoms.append((o, f"шаг {step}", 0, sup))
        if not atoms:
            print(f"в цепи {args.chain} нет разбираемых имён", file=sys.stderr)
            return 2
    else:
        q = "select name, kind, n_files from atom"
        if args.kinds:
            ks = ",".join("'" + k.strip() + "'" for k in args.kinds.split(",") if k.strip())
            q += f" where kind in ({ks})"
        q += " order by n_files desc"
        if args.limit:
            q += f" limit {args.limit}"
        atoms = con.execute(q).fetchall()

    print(f"атомов к разбору: {len(atoms)}")
    print(f"источники: Mathlib {'есть' if MATHLIB.is_dir() else 'НЕТ'} · "
          f"наше дерево {'есть' if OURS.is_dir() else 'НЕТ'} · "
          f"внешних баз {len(bases)}"
          + (": " + ", ".join(b for b, _ in bases) if bases else ""))
    print()

    # CRITICAL, поймано ревью Codex 2026-08-12: счётчик был словарём с тремя
    # фиксированными ключами, а реестр баз даёт произвольные id («zeta23»).
    # Любое имя, найденное во внешней базе, роняло прогон с KeyError. Counter
    # исключает этот класс: неизвестный ключ создаётся, а не падает.
    out = []
    stats: collections.Counter = collections.Counter()
    prov_stats: collections.Counter = collections.Counter()
    env_failures: list[str] = []
    env_path = Path(args.env_index)
    env_index: dict[str, dict] | None = None
    env_index_mtime = 0.0
    env_required = False
    env_load_error: str | None = None
    for idx, row in enumerate(atoms, 1):
        name, kind, n_files = row[0], row[1], row[2]
        supplier = row[3] if len(row) > 3 else None
        rec = {"name": name, "our_kind": kind, "our_n_files": n_files}
        cands = resolve_all(name, [("mathlib", MATHLIB), ("ours", OURS)] + bases)
        found = pick_candidate(cands)
        prov = provenance(name, cands)
        rec["provenance"] = prov
        prov_stats[prov] += 1
        # Адрес выдаётся ТОЛЬКО для настоящих деклараций. Локальная гипотеза и проза
        # адреса не имеют: любой найденный для них file:line — ложный друг.
        if prov == "LEAN_DECL" and found:
            description = found[1]
            is_routeb = (found[0] == "ours"
                         and "q3.lean.aristotle/Q3/Proofs/RouteB/"
                         in description.get("file", ""))
            if is_routeb:
                env_required = True
                try:
                    # Mathlib-only/foreign-only запросы не зависят от EnvDump.
                    # Для первой RouteB-декларации индекс становится обязательным.
                    if env_index is None:
                        if env_load_error is not None:
                            raise EnvIndexError(env_load_error)
                        try:
                            env_index = load_env_index(env_path)
                            env_index_mtime = env_path.stat().st_mtime
                        except (OSError, UnicodeError, EnvIndexError) as exc:
                            env_load_error = str(exc)
                            raise EnvIndexError(env_load_error) from exc
                    description = enrich_from_env(
                        name, description, env_index, env_index_mtime)
                    stats["lean-env"] += 1
                except (OSError, UnicodeError, EnvIndexError) as exc:
                    # Адрес исходника остаётся полезным, но текстовая сигнатура не
                    # выдаётся за elaborated type. Наличие хотя бы одной такой строки
                    # запрещает публикацию JSON ниже.
                    description = dict(description)
                    description["source_signature"] = description.pop("signature", "")
                    description["description_source"] = "UNVERIFIED_SOURCE_TEXT"
                    description["environment_error"] = str(exc)
                    env_failures.append(str(exc))
            rec.update(description); rec["source"] = found[0]; stats[found[0]] += 1
        else:
            rec["source"] = prov
            stats["unresolved"] += 1
            if found:
                rec["rejected_match"] = f"{found[1]['file']}:{found[1]['line']}"
            if prov == "AMBIGUOUS":
                rec["candidates"] = [f"{c[1]['file']}:{c[1]['line']}" for c in cands]
        out.append(rec)
        if sys.stdout.isatty() and idx % 10 == 0:
            frac = idx / len(atoms)
            bar = "#" * int(30 * frac) + "." * (30 - int(30 * frac))
            sys.stdout.write(f"\r[{bar}] {100*frac:5.1f}%  {name[:34]:<34}")
            sys.stdout.flush()
    if sys.stdout.isatty():
        print()

    print()
    print(f"  найдено в Mathlib   : {stats['mathlib']}")
    print(f"  найдено у нас       : {stats['ours']}")
    print(f"  elaborated из env   : {stats['lean-env']}")
    if env_index is not None:
        print(f"  env_index загружен  : {len(env_index)} · {env_path}")
    elif env_required:
        print(f"  env_index           : ОБЯЗАТЕЛЕН, НО НЕВАЛИДЕН · {env_path}")
    else:
        print("  env_index           : не нужен (RouteB-деклараций в запросе нет)")
    for bid, _ in bases:
        print(f"  найдено в {bid:<10}: {stats[bid]}")
    print(f"  НЕ РАЗРЕШЕНО        : {stats['unresolved']}   ← дыры нашего разбора до атомов")
    if prov_stats:
        print()
        print("── провенанс (таксономия вердикта HERMFACT1_AUDIT) ──")
        for k in sorted(prov_stats):
            print(f"  {k:<18} {prov_stats[k]}")
        rej = [r for r in out if r.get("rejected_match")]
        if rej:
            print()
            print(f"  ОТВЕРГНУТО ложных совпадений: {len(rej)}")
            for r in rej[:6]:
                print(f"    {r['name']:<24} {r['provenance']:<18} было бы {r['rejected_match']}")
    print()

    with_doc = [r for r in out if r.get("docstring")]
    print(f"  с докстрингом       : {len(with_doc)} из {len(out)}")
    print()
    print("── примеры разобранных атомов ──")
    for r in with_doc[:5]:
        print(f"  {r['name']}  [{r['our_kind']} · {r['source']}]")
        print(f"    {r['file']}:{r['line']}")
        if r.get("signature"):
            print(f"    сигнатура: {r['signature'][:110]}")
        print(f"    описание : {r['docstring'][:110]}")
        print()

    if env_failures:
        print("LEAN_ENV_DESCRIPTION_INCOMPLETE:", file=sys.stderr)
        for failure in env_failures[:20]:
            print(f"  {failure}", file=sys.stderr)
        if len(env_failures) > 20:
            print(f"  ... ещё {len(env_failures) - 20}", file=sys.stderr)
        if args.json:
            print(f"JSON не опубликован: {args.json}", file=sys.stderr)
        return 1

    if args.json:
        write_json_atomic(Path(args.json), out)
        print(f"JSON: {args.json}")

    print("Докстринг — пересказ автора, не проверка применимости. Перед употреблением "
          "открыть file:line.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
