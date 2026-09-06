#!/usr/bin/env python3
"""Append a compact chat-insight entry to a markdown knowledge base file."""

from __future__ import annotations

import argparse
from datetime import datetime
from pathlib import Path
import re
import sys

HEADER = """# Personal Insights Knowledge Base

Короткие выжимки по недавним сообщениям чата.

"""

DEFAULT_WINDOW = "последние 5-10 сообщений"
ROLE_LINE_RE = re.compile(
    r"^\s*(?:\[)?"
    r"(user|assistant|system|tool|пользователь|ассистент|система)"
    r"(?:\])?\s*:\s*(.*)$",
    re.IGNORECASE,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Append chat insights to docs/insides_knowledge_base_personal.md"
    )
    parser.add_argument(
        "--output",
        default="docs/insides_knowledge_base_personal.md",
        help="Path to output markdown file",
    )
    parser.add_argument(
        "--window",
        default=DEFAULT_WINDOW,
        help="Window description for the summary",
    )
    parser.add_argument(
        "--title",
        default="без названия",
        help="Short topic title",
    )
    parser.add_argument(
        "--tag",
        action="append",
        default=[],
        help="Tag value, can be repeated",
    )
    parser.add_argument(
        "--input-file",
        help="Read insights from file instead of stdin",
    )
    parser.add_argument(
        "--from-chat-file",
        help="Read chat export and auto-build insights from latest messages",
    )
    parser.add_argument(
        "--messages-window",
        type=int,
        default=10,
        help="How many latest messages to analyze in --from-chat-file mode",
    )
    parser.add_argument(
        "--max-insights",
        type=int,
        default=8,
        help="Maximum number of generated insights in --from-chat-file mode",
    )
    return parser.parse_args()


def read_manual_insights(input_file: str | None) -> list[str]:
    if input_file:
        raw = Path(input_file).read_text(encoding="utf-8")
    else:
        raw = sys.stdin.read()

    lines: list[str] = []
    for line in raw.splitlines():
        text = line.strip()
        if not text:
            continue
        if text.startswith("- "):
            lines.append(text)
        else:
            lines.append(f"- {text}")
    return lines


def normalize_role(role: str) -> str:
    role_l = role.lower()
    mapping = {
        "пользователь": "user",
        "ассистент": "assistant",
        "система": "system",
    }
    return mapping.get(role_l, role_l)


def compact_text(text: str, limit: int = 220) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) <= limit:
        return text
    return text[: limit - 1].rstrip() + "…"


def parse_chat_messages(raw: str) -> list[tuple[str, str]]:
    messages: list[tuple[str, str]] = []
    current_role: str | None = None
    current_lines: list[str] = []

    def flush() -> None:
        nonlocal current_role, current_lines
        if current_role is None:
            return
        joined = compact_text(" ".join(line for line in current_lines if line.strip()))
        if joined:
            messages.append((current_role, joined))
        current_role = None
        current_lines = []

    for line in raw.splitlines():
        stripped = line.strip()
        if (current_role is None or current_role == "unknown") and stripped.startswith("#"):
            if current_role == "unknown":
                flush()
            continue

        match = ROLE_LINE_RE.match(line)
        if match:
            flush()
            current_role = normalize_role(match.group(1))
            tail = match.group(2).strip()
            current_lines = [tail] if tail else []
            continue

        if not line.strip():
            if current_role == "unknown":
                flush()
            elif current_role is not None and current_lines:
                current_lines.append(" ")
            continue

        if current_role is None:
            current_role = "unknown"
            current_lines = [line.strip()]
        else:
            current_lines.append(line.strip())

    flush()

    if messages:
        return messages

    # Fallback 1: split plain text export into blocks.
    fallback: list[tuple[str, str]] = []
    for block in raw.split("\n\n"):
        clean = compact_text(block)
        if clean:
            fallback.append(("unknown", clean))
    if len(fallback) > 1:
        return fallback

    # Fallback 2: line-level extraction for markdown-like exports.
    line_fallback: list[tuple[str, str]] = []
    for line in raw.splitlines():
        clean = line.strip()
        if not clean:
            continue
        if clean.startswith("#"):
            continue
        clean = re.sub(r"^[-*]\s+", "", clean)
        clean = re.sub(r"^\d+\.\s+", "", clean)
        clean = compact_text(clean)
        if len(clean) < 12:
            continue
        line_fallback.append(("unknown", clean))

    return line_fallback or fallback


def classify_line(text: str, role: str) -> str:
    low = text.lower()
    has_command = bool(
        re.search(r"`(?:cd|git|lake|python3|tmux|systemctl|tail|rg|./)[^`]*`", text)
        or re.search(r"(^|\s)(cd|git|lake|python3|tmux|systemctl|tail|rg|\./\S+)(\s|$)", text)
    )
    has_risk = any(
        k in low
        for k in (
            "error",
            "fail",
            "timeout",
            "ошиб",
            "упал",
            "блокер",
            "oom",
            "killed",
            "warning",
        )
    )
    has_next = any(
        k in low
        for k in (
            "нужно",
            "надо",
            "сделать",
            "добавить",
            "запусти",
            "следующ",
            "план",
            "шаг",
        )
    )

    if has_command:
        prefix = "Команда/путь"
    elif has_risk:
        prefix = "Риск/сбой"
    elif has_next:
        prefix = "Следующий шаг"
    elif role == "user":
        prefix = "Запрос"
    else:
        prefix = "Факт"
    return f"- {prefix}: {compact_text(text)}"


def build_insights_from_chat(
    chat_file: str, messages_window: int, max_insights: int
) -> list[str]:
    raw = Path(chat_file).read_text(encoding="utf-8")
    messages = parse_chat_messages(raw)
    if not messages:
        return []

    selected = messages[-messages_window:]
    lines: list[str] = []
    seen: set[str] = set()

    for role, text in selected:
        if len(lines) >= max_insights:
            break
        if len(text) < 12:
            continue
        insight = classify_line(text, role)
        key = insight.lower()
        if key in seen:
            continue
        lines.append(insight)
        seen.add(key)

    return lines


def ensure_header(path: Path) -> None:
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(HEADER, encoding="utf-8")


def build_entry(window: str, title: str, tags: list[str], insights: list[str]) -> str:
    ts = datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")
    chunks = [f"## {ts} | окно: {window}\n", f"Тема: {title}\n"]

    if tags:
        tag_line = " ".join(f"#{tag}" for tag in tags)
        chunks.append(f"Теги: {tag_line}\n")

    chunks.append("Инсайты:\n")
    chunks.extend(f"{line}\n" for line in insights)
    chunks.append("\n")
    return "".join(chunks)


def main() -> int:
    args = parse_args()

    if args.from_chat_file and args.input_file:
        print(
            "[ERROR] Нельзя одновременно использовать --input-file и --from-chat-file.",
            file=sys.stderr,
        )
        return 1
    if args.messages_window < 1:
        print("[ERROR] --messages-window должен быть >= 1.", file=sys.stderr)
        return 1
    if args.max_insights < 1:
        print("[ERROR] --max-insights должен быть >= 1.", file=sys.stderr)
        return 1

    window = args.window
    if args.from_chat_file:
        insights = build_insights_from_chat(
            args.from_chat_file, args.messages_window, args.max_insights
        )
        if window == DEFAULT_WINDOW:
            window = (
                f"последние {args.messages_window} сообщений "
                f"(из файла {Path(args.from_chat_file).name})"
            )
    else:
        insights = read_manual_insights(args.input_file)

    if not insights:
        print("[ERROR] Нет инсайтов для записи.", file=sys.stderr)
        return 1

    output = Path(args.output)
    ensure_header(output)

    entry = build_entry(window, args.title, args.tag, insights)
    with output.open("a", encoding="utf-8") as fh:
        fh.write(entry)

    print(f"[OK] Записано {len(insights)} инсайтов в {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
