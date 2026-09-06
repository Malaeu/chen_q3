#!/usr/bin/env python3
"""Export Codex chat messages from local session logs to a markdown file."""

from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path
import sys


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Export current Codex session (all or last N messages)"
    )
    parser.add_argument(
        "count",
        nargs="?",
        type=int,
        help="If provided, export only the last N user/assistant messages",
    )
    parser.add_argument(
        "--session-id",
        help="Explicit session id. By default uses latest from ~/.codex/session_index.jsonl",
    )
    parser.add_argument(
        "--output",
        default="session_exports/chat_latest.md",
        help="Output markdown path",
    )
    parser.add_argument(
        "--codex-home",
        default=str(Path("~/.codex").expanduser()),
        help="Codex home directory",
    )
    return parser.parse_args()


def read_jsonl(path: Path) -> list[dict]:
    rows: list[dict] = []
    with path.open("r", encoding="utf-8") as fh:
        for line in fh:
            text = line.strip()
            if not text:
                continue
            try:
                rows.append(json.loads(text))
            except json.JSONDecodeError:
                continue
    return rows


def get_latest_session_id(index_path: Path) -> str | None:
    if not index_path.exists():
        return None
    rows = read_jsonl(index_path)
    if not rows:
        return None
    last = rows[-1]
    sid = last.get("id")
    return sid if isinstance(sid, str) and sid else None


def find_session_file(codex_home: Path, session_id: str | None) -> tuple[Path | None, str | None]:
    sessions_root = codex_home / "sessions"
    if not sessions_root.exists():
        return None, session_id

    if session_id:
        matches = sorted(sessions_root.rglob(f"*{session_id}*.jsonl"))
        if matches:
            return matches[-1], session_id

    all_logs = sorted(sessions_root.rglob("*.jsonl"))
    if not all_logs:
        return None, session_id

    latest = max(all_logs, key=lambda p: p.stat().st_mtime)
    stem = latest.stem
    guessed_id = stem.split("-")[-5:]
    if len(guessed_id) == 5:
        session_id = "-".join(guessed_id)
    return latest, session_id


def extract_messages(events: list[dict]) -> list[dict]:
    messages: list[dict] = []
    for event in events:
        if event.get("type") != "response_item":
            continue
        payload = event.get("payload")
        if not isinstance(payload, dict):
            continue
        if payload.get("type") != "message":
            continue
        role = payload.get("role")
        if role not in {"user", "assistant"}:
            continue

        content = payload.get("content")
        if not isinstance(content, list):
            continue

        chunks: list[str] = []
        for item in content:
            if not isinstance(item, dict):
                continue
            text = item.get("text")
            if isinstance(text, str) and text.strip():
                chunks.append(text.strip())

        joined = "\n\n".join(chunks).strip()
        if not joined:
            continue

        messages.append(
            {
                "role": role,
                "text": joined,
                "timestamp": event.get("timestamp", ""),
            }
        )
    return messages


def render_export(
    session_id: str | None, session_file: Path, selected: list[dict], total_messages: int
) -> str:
    now = datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")
    lines: list[str] = []
    lines.append("# Chat Export")
    lines.append("")
    lines.append(f"Generated: {now}")
    lines.append(f"Session file: `{session_file}`")
    if session_id:
        lines.append(f"Session id: `{session_id}`")
    lines.append(f"Messages: {len(selected)} of {total_messages}")
    lines.append("")

    for i, msg in enumerate(selected, start=1):
        role = "User" if msg["role"] == "user" else "Assistant"
        ts = msg.get("timestamp") or ""
        header = f"## {i}. {role}"
        if ts:
            header += f" ({ts})"
        lines.append(header)
        lines.append("")
        lines.append(msg["text"])
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    args = parse_args()
    if args.count is not None and args.count < 1:
        print("[ERROR] count должен быть >= 1", file=sys.stderr)
        return 1

    codex_home = Path(args.codex_home).expanduser()
    sid = args.session_id or get_latest_session_id(codex_home / "session_index.jsonl")
    session_file, sid = find_session_file(codex_home, sid)
    if session_file is None:
        print("[ERROR] Не найден файл сессии в ~/.codex/sessions", file=sys.stderr)
        return 1

    events = read_jsonl(session_file)
    messages = extract_messages(events)
    if not messages:
        print("[ERROR] В сессии нет user/assistant сообщений", file=sys.stderr)
        return 1

    selected = messages[-args.count :] if args.count is not None else messages

    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        render_export(sid, session_file, selected, len(messages)),
        encoding="utf-8",
    )
    mode = "last" if args.count is not None else "all"
    print(
        f"[OK] Exported {len(selected)} messages ({mode}) to {output} "
        f"from {session_file.name}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
