#!/usr/bin/env python3
"""Clipboard-native packet transport for the Route B orchestration bus.

Commands:

    python3 orchestrator/packet.py build mythos|proshka|codex
    python3 orchestrator/packet.py ingest pasted_reply.md

`build` emits one self-contained text block to stdout.  Browser heads are
assumed to have no repository, filesystem, or GitHub access.

`ingest` preserves the pasted reply byte-for-byte in both the canonical bus and
its browser mirror, routes addressed blocks into the conductor queues, records
machine-readable metadata, and regenerates the Knowledge Spine.  It never
dispatches a lane, edits Lean, commits, or pushes.

The implementation is Python-stdlib-only and intentionally avoids shell
commands and OS-specific paths.  Set Q3_PACKET_REPO_ROOT only for isolated
testing against a repository-shaped fixture.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType


SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_REPO_ROOT = SCRIPT_DIR.parent
REPO_ROOT = Path(
    os.environ.get("Q3_PACKET_REPO_ROOT", str(DEFAULT_REPO_ROOT))
).resolve()
ORCHESTRATOR_DIR = REPO_ROOT / "orchestrator"
STATE_DIR = ORCHESTRATOR_DIR / "state"
QUEUE_DIR = STATE_DIR / "queue"
INBOX_DIR = STATE_DIR / "inbox"
SPINE_PATH = STATE_DIR / "SPINE_VIEW.md"
GOVERNOR_PATH = (
    REPO_ROOT / "q3.lean.aristotle" / "ACTIVE" / "COGNITIVE_GOVERNOR.md"
)
CANON_BUS = (
    REPO_ROOT
    / "q3.lean.aristotle"
    / "ACTIVE"
    / "requests"
    / "routeB_lamport_rh_closure"
)
MIRROR_BUS = REPO_ROOT / "docs" / "routeB_bus"

LANES = ("CODEX", "PROSHKA", "ARISTOTLE", "WAIT", "YLSHA")
HEADS = ("MYTHOS", "PROSHKA", "CODEX")
MARKER_RE = re.compile(
    r"^\s*\[\s*(?:->|-->|→)\s*(" + "|".join(LANES) + r")\s*\]\s*$",
    re.IGNORECASE | re.MULTILINE,
)
HEAD_RE = re.compile(
    r"Q3_PACKET_REPLY_V1\s+HEAD\s*=\s*(MYTHOS|PROSHKA|CODEX)\b",
    re.IGNORECASE,
)
STATUS_RE = re.compile(r"^#\s*STATUS:\s*(.+?)\s*$", re.MULTILINE)
GOAL_RE = re.compile(r"^(\d{3})([A-Z]?)_(.+)\.goal\.md$")
ANSWER_RE = re.compile(r"^(\d{3})([A-Z]?R?)_(.+)\.answer\.md$")
FENCE_RE = re.compile(r"```(?:yaml|yml|text)?\s*\n(.*?)```", re.DOTALL)
M3_RE = re.compile(r"^iteration:\s*\n((?:[ \t]+.*(?:\n|$))+)", re.MULTILINE)
CODE_RE = re.compile(r"^\s*([A-Z][A-Z0-9_ -]{1,63}):\s*(\S.*)?$")
URL_RE = re.compile(r"https?://\S+")
MARKDOWN_LINK_RE = re.compile(r"\[([^\]]+)\]\(https?://[^)]+\)")
SCREAMING_RE = re.compile(r"^[A-Z][A-Z0-9_]{5,}$")
NEGATIVE_CLOSE_RE = re.compile(r"(?:INCONCLUSIVE|WALL|KILLED)", re.IGNORECASE)
AUTOPSY_LINE_RE = re.compile(
    r"^AUTOPSY:\s*dropped=([A-Z][A-Z0-9_]*);\s*note=(\S.*)$", re.MULTILINE,
)
ANY_AUTOPSY_RE = re.compile(r"^AUTOPSY:", re.MULTILINE)
AUTOPSY_TAGS_V1 = {
    "SOURCE_IDENTITY", "OBJECT_IDENTITY", "DOMAIN", "QUANTIFIER",
    "NORMALIZATION", "ORIENTATION", "LOCALIZATION", "SIGN", "PARITY",
    "MULTIPLICITY", "BOUNDEDNESS", "COUPLING", "ENDPOINT", "REGULARITY",
    "COMPACTNESS", "MEASURE_VS_ALGEBRA", "SPECTRAL_ORDERING",
    "CANCELLATION", "DEPENDENCY", "TRUST",
}


class PacketError(RuntimeError):
    """Fail-closed packet error."""


@dataclass(frozen=True)
class GoalState:
    label: str
    goal_path: Path
    answer_path: Path | None
    verdict: str | None
    title: str
    guards: tuple[str, ...]

    @property
    def answered(self) -> bool:
        return self.answer_path is not None


@dataclass(frozen=True)
class ParsedReply:
    head: str
    preamble: str
    blocks: dict[str, list[str]]
    status: str | None
    verdict_codes: tuple[tuple[str, str], ...]
    m3_blocks: tuple[str, ...]


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise PacketError(f"required file is missing: {_rel(path)}") from exc
    except UnicodeDecodeError as exc:
        raise PacketError(f"file is not valid UTF-8: {path}") from exc


def _rel(path: Path) -> str:
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _slug(value: str, limit: int = 64) -> str:
    slug = re.sub(r"[^A-Za-z0-9]+", "_", value.upper()).strip("_")
    return (slug or "ROUTED_REPLY")[:limit].rstrip("_")


def _load_spine_module() -> ModuleType:
    path = ORCHESTRATOR_DIR / "spine.py"
    if not path.is_file():
        raise PacketError(f"spine adapter is missing: {_rel(path)}")
    spec = importlib.util.spec_from_file_location("q3_packet_spine", path)
    if spec is None or spec.loader is None:
        raise PacketError(f"cannot load spine adapter: {_rel(path)}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _fresh_spine_text() -> str:
    module = _load_spine_module()
    build = getattr(module, "build", None)
    if not callable(build):
        raise PacketError("spine adapter exposes no callable build()")
    text = build()
    if not isinstance(text, str):
        raise PacketError("spine build() did not return text")
    return text


def _regenerate_spine() -> None:
    module = _load_spine_module()
    write_outputs = getattr(module, "write_outputs", None)
    if callable(write_outputs):
        write_outputs()
        return
    build = getattr(module, "build", None)
    out = getattr(module, "OUT", SPINE_PATH)
    if not callable(build):
        raise PacketError("spine adapter exposes no callable build()")
    _commit_files({Path(out): build().encode("utf-8")}, replace_generated=True)


def _extract_section(text: str, heading: str) -> str:
    marker = f"## {heading}"
    start = text.find(marker)
    if start < 0:
        return f"{marker}\n(section unavailable)"
    next_heading = text.find("\n## ", start + len(marker))
    end = len(text) if next_heading < 0 else next_heading
    return text[start:end].strip()


def _extract_governor_front() -> str:
    if not GOVERNOR_PATH.is_file():
        return "governor_front: unavailable"
    text = _read_text(GOVERNOR_PATH)
    heading = "## Current Live Route Awareness"
    start = text.find(heading)
    if start < 0:
        return "governor_front: unavailable"
    fenced = FENCE_RE.search(text, start)
    if fenced is None:
        next_heading = text.find("\n## ", start + len(heading))
        end = len(text) if next_heading < 0 else next_heading
        body = text[start + len(heading) : end].strip()
        return body or "governor_front: unavailable"
    return fenced.group(1).strip()


def _parse_flat_codes(text: str) -> tuple[tuple[str, str], ...]:
    status = STATUS_RE.search(text)
    search_start = status.end() if status else 0
    codes: list[tuple[str, str]] = []
    for fence in FENCE_RE.finditer(text, search_start):
        for line in fence.group(1).splitlines():
            match = CODE_RE.match(line)
            if match and match.group(2):
                codes.append((match.group(1).strip(), match.group(2).strip()))
        if codes:
            break
    return tuple(codes)


def _answer_verdict(path: Path) -> str | None:
    text = _read_text(path)
    status = STATUS_RE.search(text)
    if status:
        return status.group(1).strip()
    for key, value in _parse_flat_codes(text):
        if key in {"PRIMARY", "PRIMARY_VERDICT", "PRIMARY_STATUS", "STATUS"}:
            return value
    for line in text.splitlines()[:8]:
        candidate = line.strip().strip("`")
        if SCREAMING_RE.fullmatch(candidate):
            return candidate
    return None


def _goal_title(text: str, fallback: str) -> str:
    for line in text.splitlines():
        if line.startswith("# "):
            return line[2:].strip()
    return fallback


def _goal_guards(text: str) -> tuple[str, ...]:
    patterns = (
        "DO_NOT_EXECUTE",
        "execute_existing_goal_as_written=false",
        "standalone_critical_path_goal=false",
        "may_be_used_as_cofinal_premise=false",
        "BACKGROUND",
        "JUDGE_PENDING",
        "BUS_010_VOID",
        "BUS_010 VOID",
        "NOT_RH",
    )
    guards: list[str] = []
    for line in text.splitlines()[:100]:
        cleaned = re.sub(r"[`>*]", "", line).strip()
        if cleaned and any(token.lower() in cleaned.lower() for token in patterns):
            if cleaned not in guards:
                guards.append(cleaned)
        if len(guards) == 5:
            break
    return tuple(guards)


def _goal_key(num: str, suffix: str) -> tuple[int, str]:
    return int(num), suffix


def _collect_goals() -> list[GoalState]:
    if not CANON_BUS.is_dir():
        raise PacketError(f"canonical bus directory is missing: {_rel(CANON_BUS)}")

    goals: dict[tuple[str, str], tuple[Path, str, str, str]] = {}
    for path in CANON_BUS.glob("*.goal.md"):
        match = GOAL_RE.match(path.name)
        if match:
            goals[(match.group(1), match.group(2))] = (
                path,
                match.group(3),
                match.group(1),
                match.group(2),
            )

    answers: dict[tuple[str, str], Path] = {}
    for path in CANON_BUS.glob("*.answer.md"):
        match = ANSWER_RE.match(path.name)
        if not match:
            continue
        num, suffix = match.group(1), match.group(2)
        base_suffix = suffix[:-1] if suffix.endswith("R") else suffix
        key = (num, base_suffix)
        if key not in goals:
            continue
        previous = answers.get(key)
        if previous is None or suffix.endswith("R"):
            answers[key] = path

    result: list[GoalState] = []
    for key, (goal_path, name, num, suffix) in goals.items():
        goal_text = _read_text(goal_path)
        answer_path = answers.get(key)
        label = f"{num}{suffix}_{name}"
        result.append(
            GoalState(
                label=label,
                goal_path=goal_path,
                answer_path=answer_path,
                verdict=_answer_verdict(answer_path) if answer_path else None,
                title=_goal_title(goal_text, label),
                guards=_goal_guards(goal_text),
            )
        )
    return sorted(
        result,
        key=lambda goal: _goal_key(
            GOAL_RE.match(goal.goal_path.name).group(1),  # type: ignore[union-attr]
            GOAL_RE.match(goal.goal_path.name).group(2),  # type: ignore[union-attr]
        ),
    )


def _front_state(goals: list[GoalState]) -> str:
    lines = ["## FRONT STATE", "", _extract_governor_front(), ""]
    if goals:
        latest = goals[-1]
        lines.extend(
            [
                f"latest bus transaction: {latest.label}",
                f"latest bus state: {'ANSWERED' if latest.answered else 'UNANSWERED'}",
                f"latest verdict: {latest.verdict or 'UNPARSED'}",
            ]
        )
    else:
        lines.append("latest bus transaction: NONE")
    lines.extend(
        [
            "transport rule: Route B remains CHALLENGER / NOT_RH",
            "transport rule: Bus 010 remains VOID unless the owner creates it",
        ]
    )
    return "\n".join(lines)


def _open_goals(goals: list[GoalState]) -> str:
    unanswered = [goal for goal in goals if not goal.answered]
    lines = ["## OPEN OR UNANSWERED PHYSICAL GOALS", ""]
    if not unanswered:
        lines.append("- NONE")
        return "\n".join(lines)
    for goal in unanswered:
        lines.append(f"- {goal.label}: {goal.title}")
        if goal.guards:
            for guard in goal.guards:
                lines.append(f"  guard: {guard}")
        else:
            lines.append("  guard: none extracted; do not infer executability")
    lines.append(
        "- Scheduling note: unanswered does not mean executable; explicit HOLD, "
        "BACKGROUND, or DO_NOT_EXECUTE guards win."
    )
    return "\n".join(lines)


def _postclose_guards() -> str:
    """Inline versioned post-close guards that constrain future consumers."""
    if not CANON_BUS.is_dir():
        return "## POST-CLOSE FRONT GUARDS\n\n- NONE"
    artifacts = sorted(
        path
        for path in CANON_BUS.glob("*.md")
        if "postclose" in path.name.lower()
    )
    lines = ["## POST-CLOSE FRONT GUARDS", ""]
    if not artifacts:
        lines.append("- NONE")
        return "\n".join(lines)
    for path in artifacts:
        lines.extend(
            [
                f"### {_rel(path)}",
                "",
                _read_text(path).strip(),
                "",
            ]
        )
    return "\n".join(lines).rstrip()


ROLE_INSTRUCTIONS = {
    "MYTHOS": """## HEAD CONTRACT — MYTHOS

You are the Route B dispatcher and route brain.  Use only the inline state
below; assume you cannot open files or links.  Decide the smallest next
transport action without promoting Route B or manufacturing Bus 010.

Reply contract:
- first line: Q3_PACKET_REPLY_V1 HEAD=MYTHOS
- route every actionable block with a standalone marker line:
  [→CODEX], [→PROSHKA], [→ARISTOTLE], [→WAIT], or [→YLSHA]
- text before the first marker is preamble
- include every required file body and validation instruction inline
- preserve scope/verifier tags and forbidden_future_moves
""",
    "PROSHKA": """## HEAD CONTRACT — PROSHKA

You are the adversarial Route B judge.  Use only the inline state below;
assume you cannot open files or links.  Do not turn advisory reasoning,
numerics, or a sufficient-condition failure into proof truth.

Reply contract:
- first line must remain: # STATUS: PROVED / CONDITIONAL / OPEN / FATAL
- immediately follow it with a machine-readable fenced block containing
  PACKET_HEAD: PROSHKA and all verdict codes
- include one `iteration:` M3 block after every nontrivial iteration
- include addressed [→...] directives when another head must act
- name the smallest gap, forbidden future move, and cheapest decisive test
""",
    "CODEX": """## HEAD CONTRACT — CODEX

You are the local Route B executor.  Use only the inline state below and the
explicit task accompanying this packet.  Do not choose a new mathematical
route, create Bus 010, touch Lean unless explicitly tasked, commit, or push.

Reply contract:
- first line: Q3_PACKET_REPLY_V1 HEAD=CODEX
- report exact files, commands, validation, verdict/failure codes, and SHA-256
- preserve CHALLENGER / NOT_RH and every explicit bus guard
- use [→PROSHKA], [→YLSHA], or [→WAIT] for required external follow-up
""",
}


def _without_links(text: str) -> str:
    text = MARKDOWN_LINK_RE.sub(r"\1", text)
    return URL_RE.sub("[external link omitted]", text)


def build_packet(head: str) -> str:
    head = head.upper()
    if head not in HEADS:
        raise PacketError(f"unknown packet head: {head}")
    goals = _collect_goals()
    spine = _fresh_spine_text()
    sections = [
        "Q3_PACKET_V1",
        f"TARGET_HEAD: {head}",
        "BRANCH: rh_clean",
        "TRANSPORT: clipboard only; this block is complete and contains no links",
        "",
        ROLE_INSTRUCTIONS[head].strip(),
        "",
        _front_state(goals),
        "",
        _postclose_guards(),
        "",
        _extract_section(
            spine, "1. Object-level kills (FAILURE_ATLAS.json)"
        ),
        "",
        _extract_section(
            spine, "2. Strategy-level kills (FAILED_STRATEGIES.yaml)"
        ),
        "",
        _extract_section(
            spine, "3. Bus strategy memory (M3 iteration blocks in verdicts)"
        ),
        "",
        _open_goals(goals),
        "",
        "## HARD TRANSPORT GUARDS",
        "",
        "- Treat all content above as inline evidence, not as links or pointers.",
        "- Do not infer RH, route promotion, or executability from bookkeeping.",
        "- Preserve explicit owner, judge, scope, verifier, and frozen-file guards.",
    ]
    payload = _without_links("\n".join(sections).rstrip() + "\n")
    if URL_RE.search(payload) or MARKDOWN_LINK_RE.search(payload):
        raise PacketError("internal error: generated packet still contains a link")
    return payload


def _split_blocks(text: str) -> tuple[str, dict[str, list[str]]]:
    matches = list(MARKER_RE.finditer(text))
    if not matches:
        return text.strip(), {}
    preamble = text[: matches[0].start()].strip()
    blocks: dict[str, list[str]] = {}
    for index, match in enumerate(matches):
        lane = match.group(1).upper()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        body = text[match.end() : end].strip()
        if body:
            blocks.setdefault(lane, []).append(body)
    return preamble, blocks


def _extract_m3(text: str) -> tuple[str, ...]:
    blocks: list[str] = []
    for match in M3_RE.finditer(text):
        block = "iteration:\n" + match.group(1).rstrip()
        if "target:" in block and "forbidden_future_move:" in block:
            blocks.append(block)
    return tuple(blocks)


def _infer_head(
    text: str,
    explicit_head: str | None,
    codes: tuple[tuple[str, str], ...],
    blocks: dict[str, list[str]],
) -> str:
    if explicit_head:
        return explicit_head.upper()
    marker = HEAD_RE.search(text)
    if marker:
        return marker.group(1).upper()
    for key, value in codes:
        if key == "PACKET_HEAD" and value.upper() in HEADS:
            return value.upper()
    if STATUS_RE.search(text):
        return "PROSHKA"
    if "MYTHOS_PROSHKA_HANDOFF" in text or "ACTIONS LOG" in text:
        return "CODEX"
    if blocks:
        return "MYTHOS"
    raise PacketError(
        "cannot infer reply head; include Q3_PACKET_REPLY_V1 HEAD=<head> "
        "or pass --head"
    )


def parse_reply(text: str, explicit_head: str | None = None) -> ParsedReply:
    preamble, blocks = _split_blocks(text)
    status_match = STATUS_RE.search(text)
    status = status_match.group(1).strip() if status_match else None
    codes = _parse_flat_codes(text)
    head = _infer_head(text, explicit_head, codes, blocks)
    if head not in HEADS:
        raise PacketError(f"unsupported reply head: {head}")
    m3_blocks = _extract_m3(text)
    if not blocks and not status and not m3_blocks and not HEAD_RE.search(text):
        raise PacketError(
            "reply has no address markers, status header, M3 block, or packet envelope"
        )
    return ParsedReply(
        head=head,
        preamble=preamble,
        blocks=blocks,
        status=status,
        verdict_codes=codes,
        m3_blocks=m3_blocks,
    )


def validate_autopsy_close_gate(text: str, verdict_label: str | None) -> str:
    matches = list(AUTOPSY_LINE_RE.finditer(text))
    any_lines = list(ANY_AUTOPSY_RE.finditer(text))
    if any_lines and len(any_lines) != len(matches):
        raise PacketError("AUTOPSY_SCHEMA_INVALID: malformed or legacy AUTOPSY line in new payload")
    for match in matches:
        if match.group(1) not in AUTOPSY_TAGS_V1:
            raise PacketError(f"AUTOPSY_SCHEMA_INVALID: unknown tag {match.group(1)}")
    if verdict_label and NEGATIVE_CLOSE_RE.search(verdict_label) and not matches:
        raise PacketError("AUTOPSY_REQUIRED_MISSING: negative close has no structured AUTOPSY line")
    return "AUTOPSY_CLOSE_GATE_PASS"


def _commit_files(
    files: dict[Path, bytes], *, replace_generated: bool = False
) -> dict[Path, bool]:
    """Atomically create an idempotent file set.

    Existing equal files are retained.  Existing unequal files fail closed,
    except for the explicitly generated Spine view.
    """
    created: dict[Path, bool] = {}
    pending: list[tuple[Path, Path]] = []
    try:
        for path, data in files.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.exists():
                if path.read_bytes() == data:
                    created[path] = False
                    continue
                if not (replace_generated and path == SPINE_PATH):
                    raise PacketError(f"refusing to overwrite different file: {_rel(path)}")
            with tempfile.NamedTemporaryFile(
                mode="wb",
                prefix=f".{path.name}.",
                suffix=".tmp",
                dir=path.parent,
                delete=False,
            ) as handle:
                handle.write(data)
                temp_path = Path(handle.name)
            pending.append((temp_path, path))

        for temp_path, path in pending:
            os.replace(temp_path, path)
            created[path] = True
        return created
    except Exception:
        for temp_path, _ in pending:
            try:
                temp_path.unlink(missing_ok=True)
            except OSError:
                pass
        raise


def _metadata(
    source_sha: str,
    bus_name: str,
    parsed: ParsedReply,
    queue_paths: list[Path],
) -> bytes:
    data = {
        "schema": "q3_clipboard_packet_ingest.v1",
        "source_sha256": source_sha,
        "head": parsed.head,
        "status": parsed.status,
        "verdict_codes": [
            {"key": key, "value": value} for key, value in parsed.verdict_codes
        ],
        "m3_blocks": list(parsed.m3_blocks),
        "addressed_lanes": {
            lane: len(bodies) for lane, bodies in sorted(parsed.blocks.items())
        },
        "bus_file": f"docs/routeB_bus/{bus_name}",
        "canonical_file": (
            "q3.lean.aristotle/ACTIVE/requests/"
            f"routeB_lamport_rh_closure/{bus_name}"
        ),
        "queue_files": [_rel(path) for path in queue_paths],
    }
    return (json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )


def ingest_reply(path: Path, explicit_head: str | None = None) -> dict[str, object]:
    if not path.is_file():
        raise PacketError(f"pasted reply is not a regular file: {path}")
    raw = path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise PacketError("pasted reply must be UTF-8") from exc
    parsed = parse_reply(text, explicit_head=explicit_head)
    source_sha = _sha256(raw)
    short_sha = source_sha[:12]
    verdict_label = parsed.status
    if not verdict_label:
        for key, value in parsed.verdict_codes:
            if key in {"PRIMARY", "PRIMARY_VERDICT", "PRIMARY_STATUS", "STATUS"}:
                verdict_label = value
                break
    validate_autopsy_close_gate(text, verdict_label)
    bus_name = (
        f"CLIPBOARD_{parsed.head}_{_slug(verdict_label or 'ROUTED_REPLY')}_"
        f"{short_sha}.md"
    )

    queue_files: dict[Path, bytes] = {}
    queue_paths: list[Path] = []
    if parsed.preamble:
        preamble_path = INBOX_DIR / parsed.head.lower() / f"packet_{short_sha}_preamble.md"
        queue_files[preamble_path] = (parsed.preamble.rstrip() + "\n").encode("utf-8")
        queue_paths.append(preamble_path)
    for lane, bodies in sorted(parsed.blocks.items()):
        for index, body in enumerate(bodies, 1):
            queue_path = (
                QUEUE_DIR
                / lane.lower()
                / f"packet_{parsed.head.lower()}_{short_sha}_{index}.md"
            )
            queue_files[queue_path] = (body.rstrip() + "\n").encode("utf-8")
            queue_paths.append(queue_path)

    metadata_path = (
        INBOX_DIR / parsed.head.lower() / f"packet_{short_sha}.metadata.json"
    )
    files = {
        CANON_BUS / bus_name: raw,
        MIRROR_BUS / bus_name: raw,
        **queue_files,
    }
    files[metadata_path] = _metadata(source_sha, bus_name, parsed, queue_paths)
    changed = _commit_files(files)
    _regenerate_spine()

    return {
        "head": parsed.head,
        "source_sha256": source_sha,
        "bus_file": _rel(CANON_BUS / bus_name),
        "mirror_file": _rel(MIRROR_BUS / bus_name),
        "metadata_file": _rel(metadata_path),
        "queued": {
            lane: len(bodies) for lane, bodies in sorted(parsed.blocks.items())
        },
        "m3_blocks": len(parsed.m3_blocks),
        "status": parsed.status,
        "verdict_codes": len(parsed.verdict_codes),
        "created_files": sum(1 for value in changed.values() if value),
        "idempotent_files": sum(1 for value in changed.values() if not value),
        "spine": _rel(SPINE_PATH),
    }


def _cmd_build(args: argparse.Namespace) -> None:
    sys.stdout.write(build_packet(args.head))


def _cmd_ingest(args: argparse.Namespace) -> None:
    result = ingest_reply(Path(args.pasted_reply), explicit_head=args.head)
    print("INGEST_OK")
    for key in (
        "head",
        "source_sha256",
        "bus_file",
        "mirror_file",
        "metadata_file",
        "status",
        "verdict_codes",
        "m3_blocks",
        "created_files",
        "idempotent_files",
        "spine",
    ):
        print(f"{key}={result[key]}")
    queued = result["queued"]
    if isinstance(queued, dict):
        for lane, count in sorted(queued.items()):
            print(f"queued_{lane}={count}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    build_parser = sub.add_parser(
        "build", help="emit one self-contained clipboard packet"
    )
    build_parser.add_argument(
        "head", choices=("mythos", "proshka", "codex"), help="target head"
    )
    build_parser.set_defaults(func=_cmd_build)

    ingest_parser = sub.add_parser(
        "ingest", help="ingest one UTF-8 head reply from the clipboard"
    )
    ingest_parser.add_argument("pasted_reply", help="path to the pasted markdown reply")
    ingest_parser.add_argument(
        "--head",
        choices=("mythos", "proshka", "codex"),
        help="explicit source head when the reply carries no reliable envelope",
    )
    ingest_parser.set_defaults(func=_cmd_ingest)

    args = parser.parse_args()
    try:
        args.func(args)
    except PacketError as exc:
        print(f"PACKET_ERROR: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
