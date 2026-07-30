#!/usr/bin/env python3
"""RELAY lane — the conductor's transport.

Reads a harvested agent message, splits it into addressed blocks, and dispatches
the ones that run locally (Codex, Aristotle).  Browser-bound blocks (Proska,
Mythos) are written to queue/ for the conductor to paste via chrome-devtools —
a script cannot drive the tabs.

Addressing grammar (announced to Mythos 2026-07-30): a line containing exactly
one of

    [->CODEX]  [->PROSHKA]  [->ARISTOTLE]  [->WAIT]  [->YLSHA]

opens a block; the block runs to the next marker or end of message.  Arrows may
be written as `->` or the unicode arrow.  Text before the first marker is
narration and is kept as `_preamble`.

Nothing here decides math.  Routing is read off the markers the deciding agents
write themselves; an unmarked message is reported, never guessed at.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ORCHESTRATOR_DIR = Path(__file__).resolve().parent
REPO_ROOT = ORCHESTRATOR_DIR.parent
STATE_DIR = ORCHESTRATOR_DIR / "state"
QUEUE_DIR = STATE_DIR / "queue"
INBOX_DIR = STATE_DIR / "inbox"
LOG_FILE = STATE_DIR / "log.jsonl"
BUS_DIR = (
    REPO_ROOT
    / "q3.lean.aristotle"
    / "ACTIVE"
    / "requests"
    / "routeB_lamport_rh_closure"
)

LANES = ("CODEX", "PROSHKA", "ARISTOTLE", "WAIT", "YLSHA")
LOCAL_LANES = ("CODEX", "ARISTOTLE")
MARKER_RE = re.compile(
    r"^\s*\[\s*(?:->|-->|→)\s*(" + "|".join(LANES) + r")\s*\]\s*$",
    re.IGNORECASE | re.MULTILINE,
)
NOISE_RE = re.compile(
    r"```\s*This block is not supported on your current device yet\.\s*```"
)


def log(msg: str) -> None:
    print(msg, flush=True)


def event(kind: str, **fields) -> None:
    """Append one line to the conductor's append-only log."""
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    record = {"ts": datetime.now(timezone.utc).isoformat(), "event": kind, **fields}
    with LOG_FILE.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, ensure_ascii=False) + "\n")


def latest_message(raw_path: Path, sender: str = "assistant") -> str:
    """Pull the newest message of `sender` out of a harvested conversation JSON."""
    data = json.loads(raw_path.read_text(encoding="utf-8"))
    if "messages" not in data:
        for key in ("result", "value", "returnValue"):
            if isinstance(data.get(key), dict) and "messages" in data[key]:
                data = data[key]
                break
    if "messages" not in data:
        log(f"FAIL_CLOSED: no messages in {raw_path}")
        sys.exit(2)
    # claude.ai says 'assistant', chatgpt says 'assistant' too; humans differ.
    wanted = [m for m in data["messages"] if m.get("sender") == sender]
    if not wanted:
        log(f"FAIL_CLOSED: no '{sender}' message in {raw_path}")
        sys.exit(2)
    return NOISE_RE.sub("", wanted[-1].get("text", "")).strip()


def split_blocks(text: str) -> dict[str, list[str]]:
    """Split an agent message into addressed blocks, preserving order."""
    matches = list(MARKER_RE.finditer(text))
    blocks: dict[str, list[str]] = {}
    if not matches:
        return {"_unaddressed": [text]}

    preamble = text[: matches[0].start()].strip()
    if preamble:
        blocks["_preamble"] = [preamble]

    for i, match in enumerate(matches):
        lane = match.group(1).upper()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[match.end() : end].strip()
        if body:
            blocks.setdefault(lane, []).append(body)
    return blocks


def cmd_route(args: argparse.Namespace) -> None:
    raw_path = Path(args.raw)
    text = latest_message(raw_path, sender=args.sender)
    blocks = split_blocks(text)

    QUEUE_DIR.mkdir(parents=True, exist_ok=True)
    stamp = args.tag or raw_path.stem

    if "_unaddressed" in blocks:
        log("UNADDRESSED: the agent wrote no [->LANE] marker.")
        log("  -> conductor must not guess a recipient; report to Ylsha or ask the")
        log("     agent to re-emit with markers.")
        log(f"  message length: {len(text)} chars")
        event("route_unaddressed", source=str(raw_path), chars=len(text))
        return

    log(f"routed {len([k for k in blocks if not k.startswith('_')])} addressed block(s)")

    # The payload an agent refers to as "the file above" lives before the first
    # marker -- keep it, or the routed instructions point at nothing.
    for body in blocks.get("_preamble", []):
        out = QUEUE_DIR / f"{stamp}_preamble.md"
        out.write_text(body, encoding="utf-8")
        log(f"  [preamble] {len(body)} chars -> {out.relative_to(REPO_ROOT)}")
        event("route_preamble", path=str(out), chars=len(body))

    for lane, bodies in blocks.items():
        if lane.startswith("_"):
            continue
        for n, body in enumerate(bodies, 1):
            target_dir = QUEUE_DIR / lane.lower()
            target_dir.mkdir(parents=True, exist_ok=True)
            out = target_dir / f"{stamp}_{n}.md"
            out.write_text(body, encoding="utf-8")
            kind = "local" if lane in LOCAL_LANES else "browser"
            log(f"  [{lane}] {len(body)} chars -> {out.relative_to(REPO_ROOT)}  ({kind})")
            event("route_block", lane=lane, path=str(out), chars=len(body))

    if "WAIT" in blocks:
        log("  WAIT block present -> hold dispatch this cycle")
    if "YLSHA" in blocks:
        log("  YLSHA block present -> owner decision required, escalate")


def cmd_codex(args: argparse.Namespace) -> None:
    prompt_path = Path(args.file)
    prompt = prompt_path.read_text(encoding="utf-8")
    cmd = [
        "codex",
        "exec",
        "-m",
        "gpt-5.6-sol",
        "-c",
        "model_reasoning_effort=xhigh",
        "-C",
        str(REPO_ROOT),
        prompt,
    ]
    log(f"dispatching Codex on {prompt_path.name} ({len(prompt)} chars)")
    if args.dry_run:
        log("DRY RUN -- not executed. Command:")
        log("  " + " ".join(cmd[:-1]) + f" <{len(prompt)} char prompt>")
        return
    event("codex_dispatch", prompt=str(prompt_path), chars=len(prompt))
    proc = subprocess.run(cmd, cwd=REPO_ROOT)
    event("codex_exit", code=proc.returncode)
    log(f"codex exited {proc.returncode}")


def cmd_aristotle(args: argparse.Namespace) -> None:
    task_path = Path(args.file)
    log(f"checking Aristotle queue before submitting {task_path.name}")
    listing = subprocess.run(
        [str(REPO_ROOT / ".venv" / "bin" / "aristotle"), "list"],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )
    busy = [
        line
        for line in listing.stdout.splitlines()
        if re.search(r"\b(RUNNING|QUEUED|PENDING)\b", line)
    ]
    if busy and not args.despite:
        log("GATE CLOSED: a contract is still in flight (one hole, one contract):")
        for line in busy:
            log(f"  {line}")
        log("  -> if this contract addresses a DIFFERENT hole, re-run with")
        log("     --despite '<reason>'; the reason is written to the log.")
        event("aristotle_gate_closed", inflight=len(busy))
        return
    if busy:
        # The rule is one contract per hole, not one contract at a time. Crossing
        # the gate is allowed only with a stated reason, and it is on the record.
        log(f"GATE CROSSED despite {len(busy)} in flight -- reason: {args.despite}")
        event("aristotle_gate_crossed", inflight=len(busy), reason=args.despite)
    else:
        log("gate open: no RUNNING/QUEUED project")
    prompt = task_path.read_text(encoding="utf-8")
    if args.dry_run:
        log(f"DRY RUN -- would submit {task_path.name} ({len(prompt)} chars)")
        return

    # The CLI's `submit` stats its positional argument to guess path-vs-text, so a
    # task this long dies on ENAMETOOLONG before it ever reaches the API, while a
    # real path is rejected outright. Go through the library instead.
    import asyncio

    from aristotlelib import Project

    event("aristotle_dispatch", task=str(task_path), chars=len(prompt))
    project = asyncio.run(Project.create(prompt=prompt))
    project_id = getattr(project, "object_id", None) or getattr(project, "id", None)
    log(f"submitted: {task_path.name}")
    log(f"ARISTOTLE_PROJECT_ID={project_id}")
    event("aristotle_submitted", project_id=str(project_id), task=str(task_path))


def cmd_file(args: argparse.Namespace) -> None:
    """Place a queued block into the canonical bus under its real name."""
    src = Path(args.source)
    dest = BUS_DIR / args.name
    if dest.exists() and not args.force:
        log(f"REFUSING: {dest.name} already on the bus (pass --force to overwrite)")
        sys.exit(1)
    dest.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
    log(f"filed {src.name} -> {dest.relative_to(REPO_ROOT)}")
    event("bus_file", source=str(src), dest=str(dest))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_route = sub.add_parser("route", help="split a harvested message into lanes")
    p_route.add_argument("raw", help="path to a harvested *_raw.json")
    p_route.add_argument("--sender", default="assistant")
    p_route.add_argument("--tag", help="basename for the queued files")
    p_route.set_defaults(func=cmd_route)

    p_codex = sub.add_parser("codex", help="run a queued block through Codex")
    p_codex.add_argument("file")
    p_codex.add_argument("--dry-run", action="store_true")
    p_codex.set_defaults(func=cmd_codex)

    p_ar = sub.add_parser("aristotle", help="submit a task, gated on an empty queue")
    p_ar.add_argument("file")
    p_ar.add_argument("--dry-run", action="store_true")
    p_ar.add_argument(
        "--despite",
        metavar="REASON",
        help="submit even though another contract is in flight; the reason is logged",
    )
    p_ar.set_defaults(func=cmd_aristotle)

    p_file = sub.add_parser("file", help="place a queued block onto the canonical bus")
    p_file.add_argument("source")
    p_file.add_argument("name", help="target filename, e.g. 035_materialisation.goal.md")
    p_file.add_argument("--force", action="store_true")
    p_file.set_defaults(func=cmd_file)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
