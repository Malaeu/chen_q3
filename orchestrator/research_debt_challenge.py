#!/usr/bin/env python3
"""Read-only ranker and deterministic Proshka research-debt packet builder."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from orchestrator import session_briefing


def _row(repo: Path, debt_id: str) -> dict[str, Any]:
    registry = session_briefing.validate_registry(repo)
    for row in registry["debts"]:
        if row["id"] == debt_id:
            return row
    raise session_briefing.SessionBriefingError(f"RESEARCH_DEBT_UNKNOWN:{debt_id}")


def ranked(repo: Path, today: dt.date | None = None) -> list[dict[str, Any]]:
    registry = session_briefing.validate_registry(repo)
    return session_briefing.ranked_debts(
        registry["debts"], today or dt.datetime.now(dt.timezone.utc).date()
    )


def render(repo: Path, debt_id: str) -> bytes:
    row = _row(repo, debt_id)
    attempt = row["last_attempt"]
    lines = [
        "REQUEST_KIND: RESEARCH_DEBT_CHALLENGE",
        "REVIEW_GATE: REQUIRED_NOT_GRANTED_BY_THIS_PACKET",
        "DISPATCH: FORBIDDEN_UNTIL_QUEUE_OPEN_AND_REVIEW_PLAN_READY",
        f"DEBT_ID: {row['id']}",
        f"TARGET: {row['target_id']}",
        f"GOAL: {row['related_goal']}",
        "CLASSIFICATION: RESEARCH_DEBT",
        "NOT_DISPROVED: true",
        "",
        "MISSING_OBJECT:",
        row["missing_object"],
        "",
        "TERMINAL_CONSUMER:",
        row["terminal_consumer"],
        "",
        "WHY_INTERESTING:",
        row["why_interesting"],
        "",
        "KNOWN:",
        row["reason"],
        f"Last attempt ({attempt['date']}): {attempt['outcome']}",
        f"Previous approach: {attempt['approach']}",
        "",
        "DO_NOT:",
        "- Do not repeat the previous approach without a materially new ingredient.",
        "- Do not assume the missing theorem, floor, rate, inverse, or bridge.",
        "- Do not treat this packet as authorization to reopen a route or make an RH claim.",
        "",
        "MISSION:",
        "Find or derive genuinely new mathematics that changes this debt's evidential state.",
        f"Preferred next probe: {row['next_probe']}",
        "",
        "NOVELTY_REQUIREMENT (satisfy at least one and name it):",
    ]
    lines.extend(f"- {item}" for item in row["novelty_requirement"])
    lines.extend([
        "",
        "ALLOWED_RESEARCH_OUTCOMES:",
        "A. Missed primary theorem or source with exact statement and interface fit.",
        "B. New derivation that supplies the missing object without assuming it.",
        "C. Weaker sufficient lemma plus an exact argument that it reaches the terminal consumer.",
        "D. Counterexample or obstruction proving the route mathematically dead.",
        "E. One precise theorem-sized sublemma that strictly reduces the debt.",
        "",
        "OPERATIVE_RESPONSE_CLASS:",
        "Return exactly one project-compatible class beginning TRY_, KILL_, or RUN_,",
        "and state which allowed research outcome (A-E) supports it.",
        "",
        "REOPEN_BOUNDARY:",
        "A result may create REOPEN_CANDIDATE only. SOURCE_VERIFIED and a separate",
        "authorized state transaction are required before REOPENED.",
        "",
        "AUTHORITATIVE_REFS:",
    ])
    for ref in row["authoritative_refs"]:
        lines.append(
            f"- {ref['path']} @ {ref['commit']} blob {ref['git_blob']}"
        )
    return ("\n".join(lines) + "\n").encode("utf-8")


def manifest(payload: bytes, debt_id: str) -> dict[str, Any]:
    return {
        "schema": "q3_research_debt_challenge_manifest.v1",
        "debt_id": debt_id,
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
        "lines": payload.count(b"\n"),
        "final_newline": payload.endswith(b"\n"),
        "payload_utf8": payload.decode("utf-8"),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["rank", "render", "manifest"])
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--debt-id")
    parser.add_argument("--as-of", type=dt.date.fromisoformat)
    args = parser.parse_args()
    repo = args.root.resolve()
    try:
        if args.command == "rank":
            result = [
                {
                    "rank": index,
                    "id": row["id"],
                    "unlock_value": row["unlock_value"],
                    "estimated_difficulty": row["estimated_difficulty"],
                    "priority": session_briefing.debt_priority(
                        row, args.as_of or dt.datetime.now(dt.timezone.utc).date()
                    )[0],
                }
                for index, row in enumerate(ranked(repo, args.as_of), start=1)
            ]
            print(json.dumps(result, ensure_ascii=False, indent=2))
            return 0
        if not args.debt_id:
            raise session_briefing.SessionBriefingError("RESEARCH_DEBT_ID_REQUIRED")
        payload = render(repo, args.debt_id)
        if args.command == "render":
            sys.stdout.buffer.write(payload)
        else:
            print(json.dumps(manifest(payload, args.debt_id), ensure_ascii=False, indent=2))
    except session_briefing.SessionBriefingError as exc:
        print(f"RESEARCH_DEBT_CHALLENGE_INVALID:{exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
