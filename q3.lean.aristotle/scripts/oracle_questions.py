#!/usr/bin/env python3
"""Address-aware journal for oracle question series."""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
from collections import defaultdict
from contextlib import contextmanager, nullcontext
from dataclasses import dataclass
from datetime import date, datetime
from pathlib import Path

SCRIPT_PATH = Path(__file__).resolve()
Q3_ROOT = SCRIPT_PATH.parents[1]
REPO_ROOT = SCRIPT_PATH.parents[2]
JOURNAL_DIR = Q3_ROOT / "ACTIVE" / "pipeline" / "oracle_questions"
INDEX_PATH = JOURNAL_DIR / "INDEX.md"
BY_ADDRESS_PATH = JOURNAL_DIR / "BY_ADDRESS.md"
VOCAB_MAP_PATH = JOURNAL_DIR / "VOCAB_MAP.md"
TEMPLATE_PATH = JOURNAL_DIR / "TEMPLATE.md"

RESERVED_FILES = {
    "INDEX.md",
    "BY_ADDRESS.md",
    "VOCAB_MAP.md",
    "TEMPLATE.md",
}

DEFAULT_STATUS = "active"
SEARCH_INTENT_SCHEMA = "q3_search_intent.v1"
SEARCH_EVIDENCE_SCHEMA = "q3_search_evidence.v1"
SEARCH_BLOCK_MAX_BYTES = 64 * 1024
SEARCH_BLOCK_BEGIN = "<!-- Q3_SEARCH_EVIDENCE_V1_BEGIN"
SEARCH_BLOCK_END = "<!-- Q3_SEARCH_EVIDENCE_V1_END -->"
SEARCH_EVIDENCE_FIELDS = {
    "schema", "intent_id", "observed_at", "mode", "purpose", "status",
    "decision", "queries", "provider_ledger", "literature", "external_lean",
    "candidates", "alias_hypotheses", "exact_fit", "errors", "metrics",
    "boundary",
}
SEARCH_BOUNDARY = (
    "TEXT_OR_SEMANTIC_MATCHES_ARE_CANDIDATES;_ONLY_DIRECT_LEAN_TYPECHECK_"
    "WITH_STANDARD_AXIOMS_ESTABLISHES_EXACT_FIT"
)

FRONTMATTER_ORDER = [
    "status",
    "date",
    "main_address",
    "related_addresses",
    "ancestor_addresses",
    "child_or_next_addresses",
    "raw_address_notation",
    "normalized_addresses",
    "address_status",
    "blocker",
    "collections",
    "tags",
    "insight_links",
    "request_nodes",
    "strong_terms",
    "empty_terms",
    "false_friend_terms",
    "opens_new_branch_terms",
    "neighbor_addresses",
]

LIST_FIELDS = {
    "related_addresses",
    "ancestor_addresses",
    "child_or_next_addresses",
    "normalized_addresses",
    "collections",
    "tags",
    "insight_links",
    "request_nodes",
    "strong_terms",
    "empty_terms",
    "false_friend_terms",
    "opens_new_branch_terms",
    "neighbor_addresses",
}


@dataclass
class Card:
    path: Path
    meta: dict[str, object]
    body: str


def ensure_journal_dir() -> None:
    JOURNAL_DIR.mkdir(parents=True, exist_ok=True)


def split_frontmatter(text: str) -> tuple[dict[str, object], str]:
    if not text.startswith("---\n"):
        return {}, text

    lines = text.splitlines()
    try:
        end = lines[1:].index("---") + 1
    except ValueError:
        return {}, text

    meta_lines = lines[1:end]
    body = "\n".join(lines[end + 1 :]).lstrip("\n")
    meta: dict[str, object] = {}
    for raw in meta_lines:
        if not raw.strip() or raw.lstrip().startswith("#") or ":" not in raw:
            continue
        key, value = raw.split(":", 1)
        meta[key.strip()] = parse_value(value.strip())
    return meta, body


def parse_value(raw: str) -> object:
    if not raw:
        return ""
    if raw in {"true", "false"}:
        return raw == "true"
    if raw.startswith("[") or raw.startswith("{") or raw.startswith('"'):
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            return raw
    if raw.startswith("'") and raw.endswith("'") and len(raw) >= 2:
        return raw[1:-1]
    return raw


def format_value(value: object) -> str:
    if isinstance(value, list):
        return json.dumps(value, ensure_ascii=False)
    if isinstance(value, bool):
        return "true" if value else "false"
    return json.dumps("" if value is None else str(value), ensure_ascii=False)


def serialize_frontmatter(meta: dict[str, object]) -> str:
    lines = ["---"]
    for key in FRONTMATTER_ORDER:
        value = meta.get(key, [] if key in LIST_FIELDS else "")
        if key in LIST_FIELDS and not isinstance(value, list):
            value = [str(value)] if str(value).strip() else []
        lines.append(f"{key}: {format_value(value)}")
    lines.append("---")
    return "\n".join(lines)


def read_card(path: Path) -> Card:
    meta, body = split_frontmatter(path.read_text(encoding="utf-8"))
    return Card(path=path, meta=meta, body=body)


def write_card(card: Card) -> None:
    text = serialize_frontmatter(card.meta) + "\n\n" + card.body.rstrip() + "\n"
    card.path.write_text(text, encoding="utf-8")


def _render_card_bytes(card: Card) -> bytes:
    return (
        serialize_frontmatter(card.meta) + "\n\n" + card.body.rstrip() + "\n"
    ).encode("utf-8")


def _assert_no_symlink_components(path: Path, root: Path) -> None:
    try:
        relative = path.absolute().relative_to(root.absolute())
    except ValueError as exc:
        raise ValueError("SEARCH_EVIDENCE_CARD_OUTSIDE_JOURNAL") from exc
    current = root.absolute()
    if current.is_symlink():
        raise ValueError("SEARCH_EVIDENCE_CARD_SYMLINK_COMPONENT")
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError("SEARCH_EVIDENCE_CARD_SYMLINK_COMPONENT")


@contextmanager
def _search_evidence_writer_lock():
    proc = subprocess.run(
        ["git", "rev-parse", "--git-path", "q3-three-body.writer.lock"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0 or not proc.stdout.strip():
        raise ValueError("SEARCH_EVIDENCE_WRITER_LOCK_UNAVAILABLE")
    lock_path = Path(proc.stdout.strip())
    if not lock_path.is_absolute():
        lock_path = REPO_ROOT / lock_path
    if lock_path.is_symlink() or not lock_path.is_file():
        raise ValueError("SEARCH_EVIDENCE_WRITER_LOCK_UNAVAILABLE")
    with lock_path.open("r") as handle:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ValueError("SEARCH_EVIDENCE_WRITER_LOCK_BUSY") from exc
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def _validate_inherited_writer_lock(fd: int) -> None:
    """Verify an inherited descriptor names the canonical lock and is held."""

    proc = subprocess.run(
        ["git", "rev-parse", "--git-path", "q3-three-body.writer.lock"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0 or not proc.stdout.strip():
        raise ValueError("SEARCH_EVIDENCE_INHERITED_WRITER_LOCK_UNAVAILABLE")
    lock_path = Path(proc.stdout.strip())
    if not lock_path.is_absolute():
        lock_path = REPO_ROOT / lock_path
    try:
        path_info = os.lstat(lock_path)
        inherited_info = os.fstat(fd)
    except OSError as exc:
        raise ValueError("SEARCH_EVIDENCE_INHERITED_WRITER_LOCK_INVALID") from exc
    if (
        stat.S_ISLNK(path_info.st_mode)
        or not stat.S_ISREG(path_info.st_mode)
        or not stat.S_ISREG(inherited_info.st_mode)
        or (path_info.st_dev, path_info.st_ino)
        != (inherited_info.st_dev, inherited_info.st_ino)
    ):
        raise ValueError("SEARCH_EVIDENCE_INHERITED_WRITER_LOCK_IDENTITY_MISMATCH")
    probe = os.open(lock_path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        probe_info = os.fstat(probe)
        if (probe_info.st_dev, probe_info.st_ino) != (
            inherited_info.st_dev,
            inherited_info.st_ino,
        ):
            raise ValueError("SEARCH_EVIDENCE_INHERITED_WRITER_LOCK_IDENTITY_MISMATCH")
        try:
            fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            pass
        else:
            fcntl.flock(probe, fcntl.LOCK_UN)
            raise ValueError("SEARCH_EVIDENCE_INHERITED_WRITER_LOCK_NOT_HELD")
    finally:
        os.close(probe)


def _atomic_card_replace(path: Path, payload: bytes, *, expected_sha256: str) -> None:
    original = os.stat(path, follow_symlinks=False)
    if (
        not stat.S_ISREG(original.st_mode)
        or hashlib.sha256(path.read_bytes()).hexdigest() != expected_sha256
    ):
        raise ValueError("SEARCH_EVIDENCE_CARD_INPUT_DRIFT")
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            temporary_stat = os.fstat(handle.fileno())
            if temporary_stat.st_uid != original.st_uid:
                raise ValueError("SEARCH_EVIDENCE_CARD_OWNERSHIP_UNPRESERVABLE")
            if temporary_stat.st_gid != original.st_gid:
                try:
                    os.fchown(handle.fileno(), -1, original.st_gid)
                except OSError as exc:
                    raise ValueError(
                        "SEARCH_EVIDENCE_CARD_OWNERSHIP_UNPRESERVABLE"
                    ) from exc
            os.fchmod(handle.fileno(), stat.S_IMODE(original.st_mode))
            adjusted = os.fstat(handle.fileno())
            if (
                (adjusted.st_uid, adjusted.st_gid)
                != (original.st_uid, original.st_gid)
                or stat.S_IMODE(adjusted.st_mode)
                != stat.S_IMODE(original.st_mode)
            ):
                raise ValueError("SEARCH_EVIDENCE_CARD_METADATA_UNPRESERVABLE")
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        current = os.stat(path, follow_symlinks=False)
        if (
            (current.st_dev, current.st_ino, current.st_mode, current.st_uid, current.st_gid)
            != (
                original.st_dev,
                original.st_ino,
                original.st_mode,
                original.st_uid,
                original.st_gid,
            )
            or hashlib.sha256(path.read_bytes()).hexdigest() != expected_sha256
        ):
            raise ValueError("SEARCH_EVIDENCE_CARD_INPUT_DRIFT")
        os.replace(temporary, path)
        replaced = os.stat(path, follow_symlinks=False)
        if (
            (replaced.st_uid, replaced.st_gid) != (original.st_uid, original.st_gid)
            or stat.S_IMODE(replaced.st_mode) != stat.S_IMODE(original.st_mode)
        ):
            raise ValueError("SEARCH_EVIDENCE_CARD_METADATA_DRIFT")
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        Path(temporary).unlink(missing_ok=True)


def slugify(text: str) -> str:
    lowered = text.lower()
    lowered = lowered.replace("->", "_")
    lowered = re.sub(r"[^a-z0-9]+", "_", lowered)
    lowered = re.sub(r"_+", "_", lowered).strip("_")
    return lowered or "oracle_question"


def is_full_address(token: str) -> bool:
    token = token.strip()
    if not token:
        return False
    if token.startswith(".") and token[1:].isdigit():
        return False
    if token.isdigit() or token.isalpha():
        return False
    if any(ch.isalpha() for ch in token) and any(ch.isdigit() for ch in token):
        return True
    if len(token) > 2 and ("." in token or "-" in token or "/" in token):
        return True
    return False


def replace_last(pattern: str, replacement: str, text: str) -> str:
    matches = list(re.finditer(pattern, text))
    if not matches:
        raise ValueError(f"Не удалось развернуть сокращение `{replacement}` на базе `{text}`.")
    last = matches[-1]
    return text[: last.start()] + replacement + text[last.end() :]


def expand_relative_token(previous: str, token: str) -> str:
    if token.startswith(".") and token[1:].isdigit():
        if "." not in previous:
            raise ValueError(f"Сокращение `{token}` нельзя применить к `{previous}`.")
        return previous.rsplit(".", 1)[0] + token
    if token.isdigit():
        return replace_last(r"\d+", token, previous)
    if token.isalpha():
        return replace_last(r"[A-Za-zА-Яа-яЁё]+", token, previous)
    return token


def expand_address_sequence(raw: str) -> list[str]:
    tokens = [part.strip() for part in re.split(r"[,\n;]+", raw) if part.strip()]
    if not tokens:
        return []

    expanded: list[str] = []
    previous: str | None = None
    for token in tokens:
        if previous is None or is_full_address(token):
            current = token
        else:
            current = expand_relative_token(previous, token)
        expanded.append(current)
        previous = current
    return expanded


def normalize_list(raw_values: list[str]) -> list[str]:
    normalized: list[str] = []
    for raw in raw_values:
        normalized.extend(expand_address_sequence(raw))
    return unique_preserve_order(normalized)


def unique_preserve_order(items: list[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for item in items:
        cleaned = item.strip()
        if not cleaned or cleaned in seen:
            continue
        seen.add(cleaned)
        result.append(cleaned)
    return result


def relative_link(from_path: Path, target: Path) -> str:
    return os.path.relpath(target, start=from_path.parent).replace("\\", "/")


def card_files() -> list[Path]:
    if not JOURNAL_DIR.exists():
        return []
    return sorted(
        [
            path
            for path in JOURNAL_DIR.glob("*.md")
            if path.name not in RESERVED_FILES
        ],
        key=lambda path: path.name,
    )


def ensure_list(meta: dict[str, object], key: str) -> list[str]:
    value = meta.get(key, [])
    if isinstance(value, list):
        return [str(item).strip() for item in value if str(item).strip()]
    if isinstance(value, str):
        if not value.strip():
            return []
        return [value.strip()]
    return []


def normalize_card_meta(meta: dict[str, object]) -> dict[str, object]:
    normalized = dict(meta)
    raw_notation = str(normalized.get("raw_address_notation", "")).strip()

    main_address = str(normalized.get("main_address", "")).strip()
    related = normalize_list(ensure_list(normalized, "related_addresses"))
    ancestors = normalize_list(ensure_list(normalized, "ancestor_addresses"))
    children = normalize_list(ensure_list(normalized, "child_or_next_addresses"))
    collections = unique_preserve_order(ensure_list(normalized, "collections"))
    tags = unique_preserve_order(ensure_list(normalized, "tags"))
    insight_links = unique_preserve_order(ensure_list(normalized, "insight_links"))
    request_nodes = unique_preserve_order(ensure_list(normalized, "request_nodes"))
    strong_terms = unique_preserve_order(ensure_list(normalized, "strong_terms"))
    empty_terms = unique_preserve_order(ensure_list(normalized, "empty_terms"))
    false_friends = unique_preserve_order(ensure_list(normalized, "false_friend_terms"))
    branch_terms = unique_preserve_order(ensure_list(normalized, "opens_new_branch_terms"))
    neighbor_addresses = normalize_list(ensure_list(normalized, "neighbor_addresses"))

    normalized_addresses = []
    if raw_notation:
        normalized_addresses.extend(expand_address_sequence(raw_notation))
    if main_address:
        normalized_addresses.append(main_address)
    normalized_addresses.extend(related)
    normalized_addresses.extend(ancestors)
    normalized_addresses.extend(children)
    normalized_addresses.extend(neighbor_addresses)
    normalized_addresses = unique_preserve_order(normalized_addresses)

    normalized["status"] = str(normalized.get("status", DEFAULT_STATUS) or DEFAULT_STATUS)
    normalized["date"] = str(normalized.get("date", date.today().isoformat()) or date.today().isoformat())
    normalized["main_address"] = main_address
    normalized["related_addresses"] = related
    normalized["ancestor_addresses"] = ancestors
    normalized["child_or_next_addresses"] = children
    normalized["raw_address_notation"] = raw_notation
    normalized["normalized_addresses"] = normalized_addresses
    normalized["address_status"] = str(normalized.get("address_status", normalized["status"]) or normalized["status"])
    normalized["blocker"] = str(normalized.get("blocker", "")).strip()
    normalized["collections"] = collections
    normalized["tags"] = tags
    normalized["insight_links"] = insight_links
    normalized["request_nodes"] = request_nodes
    normalized["strong_terms"] = strong_terms
    normalized["empty_terms"] = empty_terms
    normalized["false_friend_terms"] = false_friends
    normalized["opens_new_branch_terms"] = branch_terms
    normalized["neighbor_addresses"] = neighbor_addresses
    return normalized


def normalize_card(card: Card) -> Card:
    card.meta = normalize_card_meta(card.meta)
    return card


def generate_title(meta: dict[str, object]) -> str:
    main_address = str(meta.get("main_address", "")).strip()
    blocker = str(meta.get("blocker", "")).strip()
    if main_address and blocker:
        return f"{main_address} — {blocker}"
    return main_address or blocker or "Новая серия вопросов к оракулу"


def new_card_body(meta: dict[str, object]) -> str:
    title = generate_title(meta)
    main_address = meta.get("main_address", "")
    blocker = meta.get("blocker", "")
    return f"""# {title}

## Статус

- карточка создана;
- серия запросов ещё не отработана полностью.

## Точный блокер

{blocker or "Заполнить точный блокер."}

## Почему этот поиск нужен сейчас

Нужно зафиксировать не только сами запросы, но и причину их постановки на адресе
`{main_address}`. Это рабочая память для следующего прохода и для соседних веток.

## Что уже известно по этому адресу

- заполнить текущий математический контекст;
- добавить ссылки на уже замороженные theorem-packets и kill certificates.

## Что именно мы хотим узнать поиском

- какие формулировки уже были бесполезны;
- какие слова могут открыть соседнюю живую ветку;
- какие локальные теоремы или reviewed notes реально усиливают `{main_address}`.

## Серия запросов

| Запрос | Адрес | Зачем этот запрос | Какая ось варьируется | Сигнал | Куда привёл |
| --- | --- | --- | --- | --- | --- |
| TODO | `{main_address}` | TODO | TODO | pending | TODO |
| TODO | `{main_address}` | TODO | TODO | pending | TODO |
| TODO | `{main_address}` | TODO | TODO | pending | TODO |

## Пустые / шумовые слова

- заполнить после первой серии.

## Новые возможные комбинации слов

- заполнить после первой серии.

## Переход в INSIGHTS

- ссылка будет добавлена после синтеза.

## Следующий адресный шаг

- зафиксировать следующий узел дерева после завершения серии.
"""


def build_index(cards: list[Card]) -> str:
    lines = [
        "# Oracle Questions Index",
        "",
        "Auto-generated by `scripts/oracle_questions.py reindex`.",
        "",
        f"Всего карточек: {len(cards)}",
        "",
    ]
    if not cards:
        lines.append("- Карточек пока нет.")
        return "\n".join(lines) + "\n"

    for card in sorted(cards, key=lambda item: (str(item.meta.get("status", "")), str(item.meta.get("main_address", "")), item.path.name)):
        rel = relative_link(INDEX_PATH, card.path)
        lines.extend(
            [
                f"## `{card.meta.get('main_address', '')}` — `{card.meta.get('status', '')}`",
                "",
                f"- файл: [{card.path.name}]({rel})",
                f"- точный блокер: {card.meta.get('blocker', '') or 'не заполнен'}",
                f"- адресный статус: `{card.meta.get('address_status', '')}`",
                f"- нормализованные адреса: {format_inline_list(ensure_list(card.meta, 'normalized_addresses'))}",
                f"- теги: {format_inline_list(ensure_list(card.meta, 'tags'))}",
                "",
            ]
        )
    return "\n".join(lines) + "\n"


def format_inline_list(items: list[str]) -> str:
    if not items:
        return "—"
    return ", ".join(f"`{item}`" for item in items)


def build_by_address(cards: list[Card]) -> str:
    address_map: dict[str, dict[str, object]] = defaultdict(
        lambda: {
            "statuses": set(),
            "parents": set(),
            "children": set(),
            "cards": [],
            "insights": set(),
            "requests": set(),
            "neighbors": set(),
        }
    )

    for card in cards:
        meta = card.meta
        main_address = str(meta.get("main_address", "")).strip()
        ancestors = ensure_list(meta, "ancestor_addresses")
        children = ensure_list(meta, "child_or_next_addresses")
        related = ensure_list(meta, "related_addresses")
        neighbors = ensure_list(meta, "neighbor_addresses")
        insights = ensure_list(meta, "insight_links")
        requests = ensure_list(meta, "request_nodes")
        card_ref = {
            "name": card.path.name,
            "path": card.path,
            "main": main_address,
            "status": meta.get("status", ""),
        }
        for address in ensure_list(meta, "normalized_addresses"):
            entry = address_map[address]
            entry["statuses"].add(str(meta.get("address_status", "")))
            entry["cards"].append(card_ref)
            entry["insights"].update(insights)
            entry["requests"].update(requests)

            if address == main_address:
                entry["parents"].update(ancestors)
                entry["children"].update(children)
                entry["neighbors"].update(related)
                entry["neighbors"].update(neighbors)
            if address in ancestors:
                entry["children"].add(main_address)
            if address in children:
                entry["parents"].add(main_address)
            if address in related:
                entry["neighbors"].add(main_address)
                entry["neighbors"].update(item for item in related if item != address)
                entry["neighbors"].update(neighbors)
            if address in neighbors:
                entry["neighbors"].add(main_address)
                entry["neighbors"].update(item for item in neighbors if item != address)

    lines = [
        "# Oracle Questions by Address",
        "",
        "Auto-generated by `scripts/oracle_questions.py reindex`.",
        "",
    ]
    if not address_map:
        lines.append("- Адресов пока нет.")
        return "\n".join(lines) + "\n"

    for address in sorted(address_map):
        entry = address_map[address]
        statuses = sorted(status for status in entry["statuses"] if status)
        parents = sorted(parent for parent in entry["parents"] if parent and parent != address)
        children = sorted(child for child in entry["children"] if child and child != address)
        insights = sorted(entry["insights"])
        requests = sorted(entry["requests"])
        neighbors = sorted(neighbor for neighbor in entry["neighbors"] if neighbor and neighbor != address)
        lines.extend(
            [
                f"## `{address}`",
                "",
                f"- статус: `{', '.join(statuses) if statuses else 'unknown'}`",
                f"- родители: {format_inline_list(parents)}",
                f"- дети / следующий шаг: {format_inline_list(children)}",
                f"- соседние адреса: {format_inline_list(neighbors)}",
                "- карточки:",
            ]
        )
        for card_ref in sorted(entry["cards"], key=lambda item: (item["status"], item["name"])):
            rel = relative_link(BY_ADDRESS_PATH, card_ref["path"])
            role = "main" if card_ref["main"] == address else "related"
            lines.append(f"  - [{card_ref['name']}]({rel}) — `{card_ref['status']}` ({role})")
        lines.append("- связанные INSIGHTS:")
        if insights:
            for insight in insights:
                lines.append(f"  - `{insight}`")
        else:
            lines.append("  - —")
        lines.append("- связанные request nodes:")
        if requests:
            for request in requests:
                lines.append(f"  - `{request}`")
        else:
            lines.append("  - —")
        if "killed" in statuses:
            lines.extend(
                [
                    "- killed subtree: этот адрес считается убитым вместе с поддеревом, если не записано обратное.",
                ]
            )
        lines.append("")
    return "\n".join(lines) + "\n"


def build_vocab_map(cards: list[Card]) -> str:
    vocab: dict[str, dict[str, set[str]]] = defaultdict(
        lambda: {
            "strong_terms": set(),
            "empty_terms": set(),
            "false_friend_terms": set(),
            "opens_new_branch_terms": set(),
            "neighbor_addresses": set(),
        }
    )

    for card in cards:
        meta = card.meta
        addresses = ensure_list(meta, "normalized_addresses")
        if not addresses:
            continue
        for address in addresses:
            entry = vocab[address]
            entry["strong_terms"].update(ensure_list(meta, "strong_terms"))
            entry["empty_terms"].update(ensure_list(meta, "empty_terms"))
            entry["false_friend_terms"].update(ensure_list(meta, "false_friend_terms"))
            entry["opens_new_branch_terms"].update(ensure_list(meta, "opens_new_branch_terms"))
            entry["neighbor_addresses"].update(ensure_list(meta, "neighbor_addresses"))
            entry["neighbor_addresses"].update(ensure_list(meta, "related_addresses"))

    lines = [
        "# Oracle Vocabulary Map",
        "",
        "Auto-generated by `scripts/oracle_questions.py reindex`.",
        "",
    ]
    if not vocab:
        lines.append("- Словарь пока пуст.")
        return "\n".join(lines) + "\n"

    for address in sorted(vocab):
        entry = vocab[address]
        lines.extend(
            [
                f"## `{address}`",
                "",
                f"- сильные слова: {format_inline_list(sorted(entry['strong_terms']))}",
                f"- пустые слова: {format_inline_list(sorted(entry['empty_terms']))}",
                f"- ложные ассоциации: {format_inline_list(sorted(entry['false_friend_terms']))}",
                f"- слова, которые открывают новую ветку: {format_inline_list(sorted(entry['opens_new_branch_terms']))}",
                f"- полезные соседние адреса: {format_inline_list(sorted(addr for addr in entry['neighbor_addresses'] if addr and addr != address))}",
                "",
            ]
        )
    return "\n".join(lines) + "\n"


def ensure_template() -> None:
    if TEMPLATE_PATH.exists():
        return
    template = """# Шаблон карточки вопроса к оракулу

Карточка должна иметь frontmatter и адресное тело. Поля ниже обязательны.

```text
---
status: "active"
date: "2026-04-12"
main_address: "PO3a.3"
related_addresses: ["PO3a.2", "PO3a.4"]
ancestor_addresses: ["PO3a", "H-bridge.11"]
child_or_next_addresses: ["PO3a.4"]
raw_address_notation: "PO3a.2, 3, 4; D2Q3B5, 7"
normalized_addresses: ["PO3a.2", "PO3a.3", "PO3a.4", "D2Q3B5", "D2Q3B7"]
address_status: "active"
blocker: "Короткое имя точного блокера"
collections: ["q3_docs", "math_papers"]
tags: ["po3", "boundary"]
insight_links: ["q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md"]
request_nodes: ["q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md"]
strong_terms: ["boundary word", "sign-pure"]
empty_terms: ["generic classification"]
false_friend_terms: ["stieltjes monotonicity"]
opens_new_branch_terms: ["volterra word"]
neighbor_addresses: ["PO3a.2", "PO3a.4"]
---
```

Обязательные разделы тела:

1. `Точный блокер`
2. `Почему этот поиск нужен сейчас`
3. `Что уже известно по этому адресу`
4. `Что именно мы хотим узнать поиском`
5. `Серия запросов`
6. `Пустые / шумовые слова`
7. `Новые возможные комбинации слов`
8. `Переход в INSIGHTS`
9. `Следующий адресный шаг`

Правило адресов:

- `raw_address_notation` хранит буквальную рабочую запись;
- `normalized_addresses` хранит явный список адресов без сокращений;
- killed address трактуется как killed subtree, если не записано обратное.
"""
    TEMPLATE_PATH.write_text(template, encoding="utf-8")


def run_reindex(write_cards: bool = True) -> int:
    ensure_journal_dir()
    ensure_template()
    cards = [normalize_card(read_card(path)) for path in card_files()]
    if write_cards:
        for card in cards:
            write_card(card)

    INDEX_PATH.write_text(build_index(cards), encoding="utf-8")
    BY_ADDRESS_PATH.write_text(build_by_address(cards), encoding="utf-8")
    VOCAB_MAP_PATH.write_text(build_vocab_map(cards), encoding="utf-8")
    print(f"Updated {INDEX_PATH.relative_to(REPO_ROOT)}")
    print(f"Updated {BY_ADDRESS_PATH.relative_to(REPO_ROOT)}")
    print(f"Updated {VOCAB_MAP_PATH.relative_to(REPO_ROOT)}")
    return 0


def cmd_new(args: argparse.Namespace) -> int:
    ensure_journal_dir()
    ensure_template()

    raw_main = args.main_address.strip()
    main_addresses = expand_address_sequence(raw_main)
    if len(main_addresses) != 1:
        raise SystemExit("`--main-address` должен разворачиваться в один адрес.")
    main_address = main_addresses[0]

    related = normalize_list(args.related_address)
    ancestors = normalize_list(args.ancestor_address)
    children = normalize_list(args.child_address)
    raw_notation = args.raw_address_notation.strip() if args.raw_address_notation else ", ".join(
        unique_preserve_order([main_address, *related])
    )

    meta: dict[str, object] = {
        "status": args.status,
        "date": args.date,
        "main_address": main_address,
        "related_addresses": related,
        "ancestor_addresses": ancestors,
        "child_or_next_addresses": children,
        "raw_address_notation": raw_notation,
        "normalized_addresses": [],
        "address_status": args.address_status,
        "blocker": args.blocker.strip(),
        "collections": unique_preserve_order(args.collection),
        "tags": unique_preserve_order(args.tag),
        "insight_links": unique_preserve_order(args.insight_link),
        "request_nodes": unique_preserve_order(args.request_node),
        "strong_terms": unique_preserve_order(args.strong_term),
        "empty_terms": unique_preserve_order(args.empty_term),
        "false_friend_terms": unique_preserve_order(args.false_friend_term),
        "opens_new_branch_terms": unique_preserve_order(args.branch_term),
        "neighbor_addresses": normalize_list(args.neighbor_address),
    }
    meta = normalize_card_meta(meta)

    slug = slugify(args.slug or f"{main_address}_{args.blocker}")
    filename = f"{args.date.replace('-', '_')}_{slug}.md"
    path = JOURNAL_DIR / filename
    if path.exists():
        raise SystemExit(f"Карточка уже существует: {path}")

    body = new_card_body(meta)
    card = Card(path=path, meta=meta, body=body)
    write_card(card)
    print(f"Created {path.relative_to(REPO_ROOT)}")
    return run_reindex(write_cards=True)


def resolve_card_path(raw: str) -> Path:
    candidate = Path(raw)
    if candidate.is_absolute():
        return candidate
    if (REPO_ROOT / raw).exists():
        return REPO_ROOT / raw
    if (JOURNAL_DIR / raw).exists():
        return JOURNAL_DIR / raw
    raise SystemExit(f"Не удалось найти карточку: {raw}")


def cmd_close(args: argparse.Namespace) -> int:
    path = resolve_card_path(args.card)
    card = normalize_card(read_card(path))
    card.meta["status"] = args.status
    card.meta["address_status"] = args.address_status or args.status

    insight_links = ensure_list(card.meta, "insight_links")
    insight_links.extend(args.insight_link)
    card.meta["insight_links"] = unique_preserve_order(insight_links)

    child_addresses = ensure_list(card.meta, "child_or_next_addresses")
    child_addresses.extend(normalize_list(args.next_address))
    card.meta["child_or_next_addresses"] = unique_preserve_order(child_addresses)

    request_nodes = ensure_list(card.meta, "request_nodes")
    request_nodes.extend(args.request_node)
    card.meta["request_nodes"] = unique_preserve_order(request_nodes)

    card = normalize_card(card)
    write_card(card)
    print(f"Updated {path.relative_to(REPO_ROOT)}")
    return run_reindex(write_cards=True)


def canonical_hash(value: object) -> str:
    raw = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def _observation_payload(evidence: dict[str, object]) -> dict[str, object]:
    def strip_runtime(value: object) -> object:
        if isinstance(value, dict):
            return {
                key: strip_runtime(item)
                for key, item in value.items()
                if key not in {"metrics", "observation_id", "elapsed_seconds", "duration_ms"}
            }
        if isinstance(value, list):
            return [strip_runtime(item) for item in value]
        return value

    return strip_runtime(evidence)  # type: ignore[return-value]


def search_observation_identity(evidence: dict[str, object]) -> str:
    """Return the durable identity shared by the writer and parent runtime."""

    observed_at = evidence.get("observed_at")
    if not isinstance(observed_at, str) or not observed_at:
        raise ValueError("SEARCH_EVIDENCE_OBSERVATION_TIME_INVALID")
    try:
        observed = datetime.fromisoformat(observed_at)
    except ValueError as exc:
        raise ValueError("SEARCH_EVIDENCE_OBSERVATION_TIME_INVALID") from exc
    if observed.tzinfo is None:
        raise ValueError("SEARCH_EVIDENCE_OBSERVATION_TIME_INVALID")
    return canonical_hash(
        {"observed_at": observed_at, "evidence": _observation_payload(evidence)}
    )


def validate_search_intent_for_record(intent: object) -> dict[str, object]:
    path = REPO_ROOT / "scripts" / "supplier_preflight.py"
    spec = importlib.util.spec_from_file_location("q3_supplier_preflight_record", path)
    if spec is None or spec.loader is None:
        raise ValueError("SEARCH_EVIDENCE_INTENT_VALIDATOR_UNAVAILABLE")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    try:
        return module.validate_search_intent_runtime(intent, repo=REPO_ROOT)
    except Exception as exc:
        raise ValueError(f"SEARCH_EVIDENCE_INTENT_RUNTIME_INVALID:{exc}") from exc


def replay_exact_fit_for_record(intent: dict[str, object]) -> dict[str, object] | None:
    module_path = REPO_ROOT / "scripts" / "supplier_preflight.py"
    spec = importlib.util.spec_from_file_location("q3_supplier_fit_replay", module_path)
    if spec is None or spec.loader is None:
        raise ValueError("SEARCH_EVIDENCE_EXACT_FIT_REPLAY_UNAVAILABLE")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module._local_exact_fit(intent)


def validate_search_evidence(
    intent: dict[str, object], evidence: object
) -> dict[str, object]:
    if not isinstance(evidence, dict) or set(evidence) != SEARCH_EVIDENCE_FIELDS:
        raise ValueError("SEARCH_EVIDENCE_SCHEMA_FIELDS_INVALID")
    if evidence.get("schema") != SEARCH_EVIDENCE_SCHEMA:
        raise ValueError("SEARCH_EVIDENCE_SCHEMA_INVALID")
    intent_id = canonical_hash(intent)
    if evidence.get("intent_id") != intent_id:
        raise ValueError("SEARCH_EVIDENCE_INTENT_BINDING_INVALID")
    if evidence.get("mode") != intent.get("mode") or evidence.get("purpose") != intent.get("purpose"):
        raise ValueError("SEARCH_EVIDENCE_MODE_PURPOSE_DRIFT")
    if evidence.get("boundary") != SEARCH_BOUNDARY:
        raise ValueError("SEARCH_EVIDENCE_BOUNDARY_INVALID")
    if evidence.get("status") not in {"PASS", "INCOMPLETE"}:
        raise ValueError("SEARCH_EVIDENCE_STATUS_INVALID")
    if evidence.get("decision") not in {
        "EXACT_FIT", "CANDIDATES", "LOCAL_COMPLETE_NO_EXACT_FIT", "INCOMPLETE"
    }:
        raise ValueError("SEARCH_EVIDENCE_DECISION_INVALID")
    errors = evidence.get("errors")
    if not isinstance(errors, list) or not all(isinstance(item, str) for item in errors):
        raise ValueError("SEARCH_EVIDENCE_ERRORS_INVALID")
    if (evidence["status"] == "INCOMPLETE") != bool(errors):
        raise ValueError("SEARCH_EVIDENCE_STATUS_ERROR_MISMATCH")
    if (evidence["decision"] == "INCOMPLETE") != (evidence["status"] == "INCOMPLETE"):
        raise ValueError("SEARCH_EVIDENCE_DECISION_STATUS_MISMATCH")
    queries = evidence.get("queries")
    candidates = evidence.get("candidates")
    aliases = evidence.get("alias_hypotheses")
    ledger = evidence.get("provider_ledger")
    literature = evidence.get("literature")
    if not isinstance(queries, list) or not 3 <= len(queries) <= 8:
        raise ValueError("SEARCH_EVIDENCE_QUERY_LIMIT_INVALID")
    if not isinstance(candidates, list) or len(candidates) > 24:
        raise ValueError("SEARCH_EVIDENCE_CANDIDATE_LIMIT_INVALID")
    if not isinstance(aliases, list) or len(aliases) > 8:
        raise ValueError("SEARCH_EVIDENCE_ALIAS_LIMIT_INVALID")
    if not isinstance(ledger, list) or len(ledger) > 9:
        raise ValueError("SEARCH_EVIDENCE_PROVIDER_LEDGER_INVALID")
    if not isinstance(literature, list) or len(literature) > 2:
        raise ValueError("SEARCH_EVIDENCE_LITERATURE_LIMIT_INVALID")
    seen_queries: set[str] = set()
    for row in queries:
        if (
            not isinstance(row, dict)
            or set(row) != {"kind", "query", "query_sha256"}
            or not isinstance(row.get("query"), str)
            or row.get("query_sha256")
            != hashlib.sha256(str(row.get("query")).encode()).hexdigest()
            or str(row.get("query")).casefold() in seen_queries
        ):
            raise ValueError("SEARCH_EVIDENCE_QUERY_RECEIPT_INVALID")
        seen_queries.add(str(row["query"]).casefold())
    for row in candidates:
        base_fields = {
            "provider", "query", "provider_id", "title", "excerpt", "url",
            "metadata_sha256", "classification",
        }
        provider = row.get("provider") if isinstance(row, dict) else None
        expected_fields = set(base_fields)
        if provider in {
            "q3_docs", "math_papers", "zotero_lib", "knowledge-db",
            "local-literature", "lean-index", "lean-tree", "specs-docs",
        }:
            expected_fields.add("query_sha256")
        if provider == "q3_docs":
            expected_fields.update({"corpus_sha256", "collection_identity"})
        if provider in {"arxiv", "crossref"}:
            expected_fields.update({"query_sha256", "published"})
        hash_payload = (
            {
                key: row.get(key)
                for key in (
                    "provider", "provider_id", "title", "excerpt", "url", "published"
                )
            }
            if isinstance(row, dict) and provider in {"arxiv", "crossref"}
            else {
                key: value
                for key, value in row.items()
                if key not in {"metadata_sha256", "classification"}
            }
            if isinstance(row, dict)
            else {}
        )
        if (
            not isinstance(row, dict)
            or set(row) != expected_fields
            or row.get("classification")
            not in {"UNVERIFIED_CANDIDATE", "KNOWN_FALSE_FRIEND"}
            or not isinstance(row.get("metadata_sha256"), str)
            or row.get("metadata_sha256")
            != canonical_hash(hash_payload)
        ):
            raise ValueError("SEARCH_EVIDENCE_CANDIDATE_RECEIPT_INVALID")
    for row in aliases:
        if (
            not isinstance(row, dict)
            or row.get("kind") != "UNVERIFIED_ALIAS_HYPOTHESIS"
            or not isinstance(row.get("term"), str)
            or not isinstance(row.get("provenance"), str)
        ):
            raise ValueError("SEARCH_EVIDENCE_ALIAS_RECEIPT_INVALID")
    for row in ledger:
        if (
            not isinstance(row, dict)
            or not isinstance(row.get("provider"), str)
            or not isinstance(row.get("query"), str)
            or row.get("status") not in {
                "HITS", "LOCAL_ZERO", "CANDIDATES", "LOCAL_ZERO_AT_CORPUS_HASH",
                "HITS_DEDUPED", "INCOMPLETE",
            }
            or not isinstance(row.get("errors"), list)
            or (evidence["status"] == "PASS" and row.get("errors"))
        ):
            raise ValueError("SEARCH_EVIDENCE_PROVIDER_RECEIPT_INVALID")
    literature_path = REPO_ROOT / "scripts" / "literature_discovery.py"
    literature_spec = importlib.util.spec_from_file_location(
        "q3_literature_receipt_record", literature_path
    )
    if literature_spec is None or literature_spec.loader is None:
        raise ValueError("SEARCH_EVIDENCE_LITERATURE_VALIDATOR_UNAVAILABLE")
    literature_module = importlib.util.module_from_spec(literature_spec)
    literature_spec.loader.exec_module(literature_module)
    for receipt in literature:
        if (
            not isinstance(receipt, dict)
            or receipt.get("schema") != "q3_literature_discovery.v1"
            or receipt.get("boundary")
            != "UNVERIFIED_METADATA_CANDIDATES_NOT_PROOF_OR_SEMANTIC_EQUIVALENCE"
            or len(receipt.get("candidates", [])) > 24
            or len(receipt.get("queries", [])) > 8
            or len(receipt.get("provider_rows", []))
            > 2 * len(receipt.get("queries", []))
            or any(
                not isinstance(row, dict)
                or row.get("status")
                not in {"CANDIDATES", "HITS_DEDUPED", "ZERO_HITS_AT_TIME", "INCOMPLETE"}
                for row in receipt.get("provider_rows", [])
            )
        ):
            raise ValueError("SEARCH_EVIDENCE_LITERATURE_RECEIPT_INVALID")
        valid_literature, literature_errors = literature_module.validate_receipt(
            receipt,
            expected_queries=receipt["queries"],
            expected_providers=tuple(receipt["providers"]),
        )
        if not valid_literature:
            raise ValueError(
                "SEARCH_EVIDENCE_LITERATURE_RECEIPT_INVALID:"
                + ";".join(literature_errors)
            )
    external = evidence.get("external_lean")
    if external is not None and (
        not isinstance(external, dict)
        or external.get("schema") != "q3_external_lean_search.v3"
        or external.get("boundary")
        not in {
            "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE",
            "INCOMPLETE_EXTERNAL_LEAN_SEARCH",
        }
    ):
        raise ValueError("SEARCH_EVIDENCE_EXTERNAL_RECEIPT_INVALID")
    if isinstance(external, dict):
        if len(external.get("queries", [])) > 8 or any(
            not isinstance(row, dict)
            or row.get("identity_before") != row.get("identity_after")
            or row.get("identity_after") != row.get("identity_final")
            for row in external.get("base_results", [])
        ):
            raise ValueError("SEARCH_EVIDENCE_EXTERNAL_IDENTITY_INVALID")
        if evidence["status"] == "PASS" and (
            external.get("errors") != []
            or external.get("boundary")
            != "CANDIDATE_MATCH_NOT_LEAN_PROOF_OR_INTERFACE_EQUIVALENCE"
        ):
            raise ValueError("SEARCH_EVIDENCE_EXTERNAL_INCOMPLETE_ON_PASS")
        external_path = REPO_ROOT / "scripts" / "search_external_lean.py"
        external_spec = importlib.util.spec_from_file_location(
            "q3_external_receipt_record", external_path
        )
        if external_spec is None or external_spec.loader is None:
            raise ValueError("SEARCH_EVIDENCE_EXTERNAL_VALIDATOR_UNAVAILABLE")
        external_module = importlib.util.module_from_spec(external_spec)
        external_spec.loader.exec_module(external_module)
        admission = intent.get("admission")
        expected_candidate = (
            admission.get("theorem") if isinstance(admission, dict) else None
        )
        expected_provenance = (
            admission.get("candidate_provenance")
            if isinstance(admission, dict)
            else None
        )
        valid_external, external_errors = external_module.validate_batch_receipt(
            external,
            expected_queries=[str(row["query"]) for row in queries],
            expected_candidate=expected_candidate,
            expected_candidate_provenance=expected_provenance,
        )
        if not valid_external:
            raise ValueError(
                "SEARCH_EVIDENCE_EXTERNAL_RECEIPT_INVALID:"
                + ";".join(external_errors)
            )
    metrics = evidence.get("metrics")
    if (
        not isinstance(metrics, dict)
        or metrics.get("qmd_subprocesses") not in range(0, 9)
        or metrics.get("external_lean_batches") not in range(0, 2)
        or metrics.get("web_batches") not in range(0, 3)
    ):
        raise ValueError("SEARCH_EVIDENCE_METRICS_INVALID")
    if evidence["decision"] == "EXACT_FIT":
        admission = intent.get("admission")
        exact_fit = evidence.get("exact_fit")
        if (
            not isinstance(admission, dict)
            or not isinstance(exact_fit, dict)
            or exact_fit.get("status") != "EXACT_FIT"
            or not isinstance(exact_fit.get("comparison"), dict)
            or exact_fit["comparison"].get("status") != "EXACT_FIT"
            or not isinstance(exact_fit["comparison"].get("candidate"), dict)
            or exact_fit["comparison"]["candidate"].get("name")
            != admission.get("theorem")
            or not isinstance(exact_fit["comparison"].get("target"), dict)
            or exact_fit["comparison"]["target"].get("name")
            != admission.get("target_declaration")
        ):
            raise ValueError("SEARCH_EVIDENCE_EXACT_FIT_INVALID")
        replay = replay_exact_fit_for_record(intent)
        if not isinstance(replay, dict) or replay.get("status") != "EXACT_FIT":
            raise ValueError("SEARCH_EVIDENCE_EXACT_FIT_REPLAY_FAILED")
    elif evidence.get("exact_fit") is not None and evidence["status"] == "PASS":
        raise ValueError("SEARCH_EVIDENCE_NONEXACT_DECISION_HAS_EXACT_FIT")
    if evidence["status"] == "PASS" and (
        (evidence["decision"] == "CANDIDATES") != bool(candidates)
        or (
            evidence["decision"] == "LOCAL_COMPLETE_NO_EXACT_FIT"
            and bool(candidates)
        )
    ):
        raise ValueError("SEARCH_EVIDENCE_DECISION_CANDIDATE_MISMATCH")
    return json.loads(json.dumps(evidence, ensure_ascii=False))


def record_search_evidence(
    card_path: Path,
    intent: object,
    evidence: object,
    *,
    inherited_writer_lock_fd: int | None = None,
) -> tuple[str, str]:
    intent = validate_search_intent_for_record(intent)
    evidence = validate_search_evidence(intent, evidence)
    intent_id = canonical_hash(intent)
    if evidence.get("intent_id") != intent_id:
        raise ValueError("SEARCH_EVIDENCE_INTENT_BINDING_INVALID")
    observation_id = search_observation_identity(evidence)
    stored = json.loads(json.dumps(evidence, ensure_ascii=False))
    stored["observation_id"] = observation_id
    rendered = json.dumps(stored, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    block = (
        f"{SEARCH_BLOCK_BEGIN} intent_id={intent_id} observation_id={observation_id} -->\n"
        f"```json\n{rendered}\n```\n{SEARCH_BLOCK_END}"
    )
    if len(block.encode("utf-8")) > SEARCH_BLOCK_MAX_BYTES:
        raise ValueError("SEARCH_EVIDENCE_MACHINE_BLOCK_TOO_LARGE")
    if card_path.is_symlink():
        raise ValueError("SEARCH_EVIDENCE_CARD_OUTSIDE_JOURNAL")
    _assert_no_symlink_components(card_path, JOURNAL_DIR)
    resolved_journal = JOURNAL_DIR.resolve(strict=True)
    resolved_card = card_path.resolve(strict=True)
    if not resolved_card.is_file() or not resolved_card.is_relative_to(resolved_journal):
        raise ValueError("SEARCH_EVIDENCE_CARD_OUTSIDE_JOURNAL")
    lock_context = _search_evidence_writer_lock()
    if inherited_writer_lock_fd is not None:
        _validate_inherited_writer_lock(inherited_writer_lock_fd)
        lock_context = nullcontext()
    with lock_context:
        _assert_no_symlink_components(resolved_card, JOURNAL_DIR)
        before = resolved_card.read_bytes()
        before_sha256 = hashlib.sha256(before).hexdigest()
        card = normalize_card(read_card(resolved_card))
        marker = f"observation_id={observation_id}"
        if marker in card.body:
            existing_pattern = re.compile(
                rf"{re.escape(SEARCH_BLOCK_BEGIN)}[^\n]*{re.escape(marker)}[^\n]*-->\n```json\n(.*?)\n```\n{re.escape(SEARCH_BLOCK_END)}",
                re.S,
            )
            match = existing_pattern.search(card.body)
            if match is None or match.group(1) != rendered:
                raise ValueError("SEARCH_EVIDENCE_OBSERVATION_COLLISION")
            return "NOOP", observation_id
        if evidence.get("decision") == "EXACT_FIT":
            admission = intent.get("admission")
            theorem = admission.get("theorem") if isinstance(admission, dict) else None
            if isinstance(theorem, str) and theorem:
                strong = ensure_list(card.meta, "strong_terms")
                strong.append(theorem)
                card.meta["strong_terms"] = unique_preserve_order(strong)
        explicit_false_friends = intent.get("known_false_friends")
        if isinstance(explicit_false_friends, list):
            terms = ensure_list(card.meta, "false_friend_terms")
            terms.extend(
                str(row.get("term"))
                for row in explicit_false_friends
                if isinstance(row, dict) and isinstance(row.get("term"), str)
            )
            card.meta["false_friend_terms"] = unique_preserve_order(terms)
        card.body = card.body.rstrip() + "\n\n## Search evidence\n\n" + block + "\n"
        _atomic_card_replace(
            resolved_card, _render_card_bytes(card), expected_sha256=before_sha256
        )
        return "RECORDED", observation_id


def cmd_record_evidence(args: argparse.Namespace) -> int:
    try:
        if args.inherited_writer_lock_fd is None:
            raise ValueError("SEARCH_EVIDENCE_INHERITED_WRITER_LOCK_REQUIRED")
        intent = json.loads(args.intent.read_text(encoding="utf-8"))
        evidence = json.loads(args.evidence.read_text(encoding="utf-8"))
        card_path = resolve_card_path(args.card)
        status, observation_id = record_search_evidence(
            card_path,
            intent,
            evidence,
            inherited_writer_lock_fd=args.inherited_writer_lock_fd,
        )
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        return 2
    print(json.dumps({"schema": "q3_search_evidence_write.v1", "status": status, "observation_id": observation_id}, sort_keys=True))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Address-aware oracle question journal.")
    sub = parser.add_subparsers(dest="command", required=True)

    new = sub.add_parser("new", help="Создать новую карточку вопроса.")
    new.add_argument("--main-address", required=True, help="Главный адрес ветки.")
    new.add_argument("--related-address", action="append", default=[], help="Связанные адреса; сокращения допускаются внутри одного аргумента.")
    new.add_argument("--ancestor-address", action="append", default=[], help="Родительские адреса; сокращения допускаются внутри одного аргумента.")
    new.add_argument("--child-address", action="append", default=[], help="Дочерние или следующие адреса; сокращения допускаются внутри одного аргумента.")
    new.add_argument("--neighbor-address", action="append", default=[], help="Полезные соседние адреса.")
    new.add_argument("--blocker", required=True, help="Короткое описание точного блокера.")
    new.add_argument("--status", default=DEFAULT_STATUS, help="Статус карточки.")
    new.add_argument("--address-status", default=DEFAULT_STATUS, help="Статус главного адреса.")
    new.add_argument("--date", default=date.today().isoformat(), help="Дата карточки в формате YYYY-MM-DD.")
    new.add_argument("--raw-address-notation", default="", help="Буквальная рабочая запись адресов.")
    new.add_argument("--collection", action="append", default=[], help="Коллекция поиска.")
    new.add_argument("--tag", action="append", default=[], help="Тег карточки.")
    new.add_argument("--insight-link", action="append", default=[], help="Связанный insight.")
    new.add_argument("--request-node", action="append", default=[], help="Связанный request node.")
    new.add_argument("--strong-term", action="append", default=[], help="Сильное слово или фраза.")
    new.add_argument("--empty-term", action="append", default=[], help="Пустое / шумовое слово.")
    new.add_argument("--false-friend-term", action="append", default=[], help="Ложная ассоциация.")
    new.add_argument("--branch-term", action="append", default=[], help="Слово, открывающее новую ветку.")
    new.add_argument("--slug", default="", help="Хвост имени файла.")
    new.set_defaults(func=cmd_new)

    reindex = sub.add_parser("reindex", help="Обновить индексы и нормализовать карточки.")
    reindex.set_defaults(func=lambda args: run_reindex(write_cards=True))

    close = sub.add_parser("close", help="Закрыть карточку и обновить индексы.")
    close.add_argument("card", help="Путь до карточки или имя файла.")
    close.add_argument("--status", default="done", help="Новый статус карточки.")
    close.add_argument("--address-status", default="", help="Новый статус адреса.")
    close.add_argument("--insight-link", action="append", default=[], help="Связанный insight.")
    close.add_argument("--next-address", action="append", default=[], help="Следующий адресный шаг.")
    close.add_argument("--request-node", action="append", default=[], help="Связанный request node.")
    close.set_defaults(func=cmd_close)

    record = sub.add_parser("record-evidence", help="Записать byte-bound supplier evidence в существующую карточку.")
    record.add_argument("--card", required=True)
    record.add_argument("--intent", type=Path, required=True)
    record.add_argument("--evidence", type=Path, required=True)
    record.add_argument("--inherited-writer-lock-fd", type=int)
    record.set_defaults(func=cmd_record_evidence)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
