#!/usr/bin/env python3
"""SENSE lane — read-only phase detection for the Route B conductor.

Build-order step 1 (ORCHESTRATION_DESIGN.md Sec.5): senses the live bus, classifies
the current goal's phase and prints the plan.  Dispatches nothing, pushes nothing,
writes nothing outside orchestrator/state/.

Canonical bus pinned to routeB_lamport_rh_closure (open item #1): the twolevel
ladder bus is dormant since 2026-07-11 at goal 009.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ORCHESTRATOR_DIR = Path(__file__).resolve().parent
REPO_ROOT = ORCHESTRATOR_DIR.parent
BUS_DIR = (
    REPO_ROOT
    / "q3.lean.aristotle"
    / "ACTIVE"
    / "requests"
    / "routeB_lamport_rh_closure"
)
MIRROR_DIR = REPO_ROOT / "docs" / "routeB_bus"
STATE_DIR = ORCHESTRATOR_DIR / "state"
STATE_FILE = STATE_DIR / "state.json"

GOAL_RE = re.compile(r"^(\d{3})_(.+)\.goal\.md$")
ANSWER_RE = re.compile(r"^(\d{3}R?)_(.+)\.answer\.md$")
CODEBLOCK_RE = re.compile(r"```(?:yaml|text)?\n(.*?)```", re.DOTALL)

# Grammar v2 (PROSHKA_SYSTEM_PROMPT_v2): `# STATUS: ...` + machine-readable block.
STATUS_V2_RE = re.compile(r"^#\s*STATUS:\s*(.+?)\s*$", re.MULTILINE)
# Legacy grammar (goals <= 033): `# ОТВЕТ NNN — ...` with the verdict as a
# backticked SCREAMING_SNAKE token, or a `Status:` line.
LEGACY_TOKEN_RE = re.compile(r"`([A-Z][A-Z0-9_]{5,})`")
LEGACY_STATUS_RE = re.compile(r"^Status:\s*(.+?)\s*$", re.MULTILINE)

# Verdict tokens the bus grammar uses (CONDUCTOR.md state machine).
DECISIVE = ("PROVED", "KILL", "ACCEPT", "LIVE", "CLOSED")
NONDECISIVE = ("OPEN", "INCONCLUSIVE", "CONDITIONAL", "REPAIR", "FATAL")


def log(msg: str) -> None:
    print(msg, flush=True)


@dataclass
class Goal:
    num: str
    name: str
    goal_path: Path
    answer_path: Path | None = None
    status_line: str | None = None
    grammar: str | None = None  # "v2" | "legacy"
    codes: dict[str, str] = field(default_factory=dict)

    @property
    def label(self) -> str:
        return f"{self.num}_{self.name}"


def parse_answer(path: Path) -> tuple[str | None, str | None, dict[str, str]]:
    """Extract the verdict from either bus grammar.

    Returns (status_line, grammar, codes).  Grammar v2 is the machine-readable
    `# STATUS:` header; legacy answers (goals <= 033) carry the verdict as a
    backticked token in the opening lines instead.
    """
    text = path.read_text(encoding="utf-8", errors="replace")

    codes: dict[str, str] = {}
    block_match = CODEBLOCK_RE.search(text)
    if block_match:
        for line in block_match.group(1).splitlines():
            if ":" not in line or line.lstrip().startswith("-"):
                continue
            key, _, value = line.partition(":")
            key, value = key.strip(), value.strip()
            if key and not key.startswith("#") and value:
                codes[key] = value

    status_match = STATUS_V2_RE.search(text)
    if status_match:
        return status_match.group(1), "v2", codes

    # Legacy: scan the opening block for the verdict token.
    head = "\n".join(text.splitlines()[:20])
    token_match = LEGACY_TOKEN_RE.search(head)
    if token_match:
        return token_match.group(1), "legacy", codes
    legacy_status = LEGACY_STATUS_RE.search(head)
    if legacy_status:
        return legacy_status.group(1), "legacy", codes

    return None, None, codes


def collect_goals() -> list[Goal]:
    if not BUS_DIR.is_dir():
        log(f"FAIL_CLOSED: bus directory missing: {BUS_DIR}")
        sys.exit(2)

    goals: dict[str, Goal] = {}
    for path in sorted(BUS_DIR.glob("*.goal.md")):
        m = GOAL_RE.match(path.name)
        if m:
            goals[m.group(1)] = Goal(num=m.group(1), name=m.group(2), goal_path=path)

    for path in sorted(BUS_DIR.glob("*.answer.md")):
        m = ANSWER_RE.match(path.name)
        if not m:
            continue
        num = m.group(1).rstrip("R")
        goal = goals.get(num)
        if goal is None:
            continue
        # A revision answer (NNNR_) supersedes the base answer.
        if goal.answer_path is None or m.group(1).endswith("R"):
            goal.answer_path = path
            goal.status_line, goal.grammar, goal.codes = parse_answer(path)

    return [goals[k] for k in sorted(goals)]


def classify(goal: Goal, state: dict, is_front: bool) -> tuple[str, str]:
    """Return (phase, next action) for a goal.

    `is_front` marks the highest-numbered goal: only there does an unreadable
    verdict block the loop.  A historical answer the parser cannot classify is
    reported as a warning, not as an open front.
    """
    inflight = {node.get("target"): node for node in state.get("inflight", [])}

    if goal.answer_path is None:
        node = inflight.get(goal.label)
        if node:
            return (
                "AWAITING_JUDGE",
                f"in flight on lane '{node.get('lane')}' since {node.get('sentAt')} "
                f"-> poll detect_complete.js, do not re-dispatch",
            )
        return (
            "AWAITING_JUDGE",
            "sync mirror, relay goal to Proska (browser), then poll ~15 min",
        )

    if goal.status_line is None:
        if is_front:
            return (
                "UNPARSABLE",
                "FAIL-CLOSED: answer carries no verdict in either grammar -> escalate to Ylsha",
            )
        return ("CLOSED_UNPARSED", "historical answer, verdict token not recognised")

    upper = goal.status_line.upper()
    primary = goal.codes.get("PRIMARY_STATUS", "").upper()
    verdict = primary or upper

    if any(tok in verdict for tok in DECISIVE):
        if not is_front:
            return ("CLOSED", "historical, decisive")
        return (
            "AWAITING_DISTRIBUTION",
            "decisive verdict -> relay to Mythos for distribution; "
            "adversarial gate before anything is trusted; never auto-escalate an RH claim",
        )
    if any(tok in verdict for tok in NONDECISIVE):
        if not is_front:
            return ("CLOSED_NONDECISIVE", "historical, non-decisive")
        return (
            "AWAITING_DISTRIBUTION",
            "non-decisive verdict -> relay to Mythos; next goal formulation is the judge's call",
        )
    if is_front:
        return (
            "UNPARSABLE",
            f"FAIL-CLOSED: unclassifiable verdict '{goal.status_line}' -> escalate",
        )
    return ("CLOSED_UNPARSED", f"historical, unclassified verdict '{goal.status_line}'")


def load_state() -> dict:
    if STATE_FILE.is_file():
        try:
            return json.loads(STATE_FILE.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            log(f"FAIL_CLOSED: state.json is not valid JSON: {exc}")
            sys.exit(2)
    return {"inflight": [], "cycle": 0}


def mirror_drift(goals: list[Goal]) -> list[str]:
    """Files the bus has that the Proska mirror does not yet carry."""
    if not MIRROR_DIR.is_dir():
        return ["mirror directory missing"]
    mirrored = {p.name for p in MIRROR_DIR.iterdir() if p.is_file()}
    missing = []
    for goal in goals:
        for path in (goal.goal_path, goal.answer_path):
            if path is not None and path.name not in mirrored:
                missing.append(path.name)
    return missing


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json", action="store_true", help="emit the sensed state as JSON"
    )
    args = parser.parse_args()

    goals = collect_goals()
    state = load_state()
    total = len(goals)

    if not args.json:
        log("=" * 72)
        log("ROUTE B CONDUCTOR -- SENSE (read-only, no dispatch, no push)")
        log("=" * 72)
        log(f"bus     : {BUS_DIR.relative_to(REPO_ROOT)}")
        log(f"mirror  : {MIRROR_DIR.relative_to(REPO_ROOT)}")
        log(f"goals   : {total}")
        log("")

    rows = []
    front_num = goals[-1].num if goals else None
    for i, goal in enumerate(goals, 1):
        phase, action = classify(goal, state, is_front=goal.num == front_num)
        rows.append(
            {
                "goal": goal.label,
                "phase": phase,
                "status": goal.status_line,
                "grammar": goal.grammar,
                "answer": goal.answer_path.name if goal.answer_path else None,
                "action": action,
                "codes": goal.codes,
            }
        )

    open_rows = [
        r
        for r in rows
        if r["phase"] in ("AWAITING_JUDGE", "AWAITING_DISTRIBUTION", "UNPARSABLE")
    ]
    unparsed = [r for r in rows if r["phase"] == "CLOSED_UNPARSED"]

    if args.json:
        print(
            json.dumps(
                {"goals": rows, "open": open_rows, "unparsed": unparsed},
                ensure_ascii=False,
                indent=2,
            )
        )
        return

    closed = total - len(open_rows)
    log(f"closed  : {closed}/{total} (historical answers on file)")
    log("")
    log("-" * 72)
    if not open_rows:
        log("NO_OPEN_BUS_GOAL / STOP -- every goal carries a classified answer.")
    for row in open_rows:
        log(f"OPEN FRONT  : {row['goal']}")
        log(f"  phase       : {row['phase']}")
        if row["answer"] is None:
            log("  answer      : none on the bus yet")
        else:
            log(f"  answer      : {row['answer']}  [grammar: {row['grammar']}]")
            log(f"  verdict     : {row['status']}")
        log(f"  next action : {row['action']}")
        if row["codes"]:
            log("  verdict codes:")
            for key, value in list(row["codes"].items())[:8]:
                log(f"      {key} = {value}")

    if unparsed:
        log("")
        log(
            f"PARSE WARNINGS: {len(unparsed)} historical answer(s) carry no recognised "
            "verdict token (not blocking):"
        )
        for row in unparsed[:6]:
            log(f"  - {row['goal']}")
        if len(unparsed) > 6:
            log(f"  ... and {len(unparsed) - 6} more")

    drift = mirror_drift(goals)
    log("")
    if drift:
        log(f"MIRROR DRIFT: {len(drift)} bus file(s) not in docs/routeB_bus/")
        for name in drift[:10]:
            log(f"  - {name}")
        log("  -> run sync_proshka_github_channel.py before relaying to Proska")
    else:
        log("MIRROR: in sync with the bus.")

    log("")
    log("RED LINE: conductor is transport only. Judge = Proska, brain = Mythos.")
    log("Push scope: docs/routeB_bus/ only (CHANNEL_RULE). No force-push, no merge to main.")


if __name__ == "__main__":
    main()
