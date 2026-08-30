#!/usr/bin/env python3
"""Lifecycle-aware scan for unjustified rigid research dependencies.

This is deliberately not a repository-wide banned-word grep.  It resolves the
small set of live policy surfaces, the current task/goal/request objects, and
the generators which can mint new dependency prose.  Assertions are judged in
their containing Markdown section (or Python function), so consumer evidence
cannot be borrowed from an unrelated paragraph elsewhere in the file.
"""

from __future__ import annotations

import ast
import json
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Iterable


STATIC_ACTIVE = (
    "docs/CODEX_CONTROL.md",
    "SESSION_ENTRY.md",
    "q3.lean.aristotle/ACTIVE/SESSION_ENTRY.md",
    "q3.lean.aristotle/COGNITIVE_KERNEL.md",
    "q3.lean.aristotle/COGNITIVE_OPERATORS.md",
    "q3.lean.aristotle/PROJECT_WORKFLOW.md",
    "q3.lean.aristotle/docs/PROJECT_INSTRUCTIONS_v3_arsenal.md",
    "q3.lean.aristotle/docs/PROSHKA_ENTRYPOINT.md",
    "q3.lean.aristotle/docs/PROSHKA_POLICY.md",
    "docs/Codex/RESEARCH_DEPENDENCY_PROTOCOL.md",
    "docs/Codex/SESSION_BRIEFING.md",
    "docs/routeB_bus/SUPPLIER_CONTRACT.md",
    "docs/routeB_bus/PROSHKA_SYSTEM_PROMPT_v2.md",
    "docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md",
    "q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/proshka/PROSHKA_SYSTEM_PROMPT_v2.md",
)

NAMED_GENERATORS = (
    "orchestrator/research_debt_challenge.py",
    "orchestrator/research_dependency_projection.py",
    "orchestrator/session_briefing.py",
    "orchestrator/workflow_runtime.py",
    "orchestrator/goal_runtime.py",
    "orchestrator/packet.py",
    "orchestrator/three_body_loop.py",
    "orchestrator/kb.py",
    "orchestrator/kb_migrate_kills.py",
    "orchestrator/kb_migrate_verdicts.py",
    "scripts/q3_docs_corpus.py",
    "scripts/build_proshka_brief.py",
)

HISTORICAL_PARTS = frozenset({"archive", "archives", "session_exports", "literature"})
HISTORICAL_NAME_RE = re.compile(
    r"(?:^|_)(?:VERDICT|ANSWER|CLOSEOUT|REPORT|PROTOKOLL)(?:_|\.|$)|\.answer\.md$",
    re.IGNORECASE,
)
NONLIVE_STATUS_RE = re.compile(
    r"(?i)^(?:CLOSED|ANSWERED|DROPPED|PAUSED(?:_RESTORABLE)?|"
    r"DONE(?:_CLOSED)?|DORMANT[^\s]*)\b"
)
STATUS_LINE_RE = re.compile(r"(?i)^\s*(?:STATUS|status)\s*:\s*([^\n#`]+)")

# Dependency words are intentionally coupled to assertion words.  Bare KILL,
# REQUIRED, theorem, or source tokens are control vocabulary and do not match.
ASSERTION_PATTERNS = (
    re.compile(
        r"(?i)\b(?:must\s+(?:prove|formalize)|required\s+(?:theorem|lemma|source|rate|floor|bridge|inverse)|"
        r"cannot\s+proceed\s+without|blocked\s+(?:on|by)\s+(?:the\s+)?|BLOCKED\s*:|"
        r"needs?\s+(?:an?\s+|the\s+|this\s+|exact\s+|uniform\s+)*(?:theorem|lemma|source|rate|floor|bridge|inverse))"
    ),
    re.compile(
        r"(?i)\b(?:route\s+(?:is|was)\s+(?:dead|wrong|impossible)|"
        r"kill(?:ing)?\s+the\s+route|proved\s+dead\s+end|no\s+return)\b"
    ),
    re.compile(r"(?i)(?:убийств\w*\s+маршрут\w*|доказанн\w*\s+тупик\w*|не\s+подлежит\s+возврату)"),
    re.compile(
        r"(?i)\b(?:EPISTEMIC_STATUS|CLASSIFICATION|DEPENDENCY_STATUS|RESULT)\s*:\s*MATHEMATICALLY_DEAD\b"
    ),
)

EXEMPTIONS = frozenset(
    {
        "BYTE_IDENTITY_OR_TRUST_BINDING",
        "FROZEN_ADMITTED_CONTRACT",
        "LEAN_TYPE_INTERFACE",
        "CONTROL_VOCABULARY_ONLY",
    }
)
EXEMPTION_RE = re.compile(r"(?im)^\s*RIGID_DEPENDENCY_EXEMPTION\s*:\s*([A-Z0-9_]+)\s*$")

FIELD_PATTERNS = {
    "consumer": re.compile(r"(?i)\b(?:DOWNSTREAM_CONSUMER|TERMINAL_CONSUMER|downstream\s+consumer|terminal\s+consumer)\b"),
    "requirement": re.compile(r"(?i)\b(?:ACTUAL_CONSUMER_REQUIREMENT|MINIMAL_SUFFICIENT_INTERFACE|actual\s+consumer\s+requirement|minimal\s+sufficient\s+interface)\b"),
    "necessity": re.compile(r"(?i)\b(?:ORIGINAL_OBJECT_IS|NECESSITY_STATUS|PROVED_NECESSARY|NOT_NECESSARY|necessity\s+(?:status|audit))\b"),
    "weaker": re.compile(r"(?i)\b(?:KNOWN_WEAKER_INTERFACES|WEAKER_INTERFACE_PROBE|weaker\s+(?:interface|lemma|theorem|contract)|alternative\s+representation)\b"),
    "implication": re.compile(r"(?i)\b(?:CONSUMER_IMPLICATION|Z\s*(?:=>|→)\s*(?:C|Y)|exact\s+(?:consumer\s+)?implication)\b"),
}


@dataclass(frozen=True)
class Surface:
    path: str
    kind: str  # markdown | generator


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    section: str
    missing: tuple[str, ...]
    assertion: str

    def render(self) -> str:
        return (
            f"RIGID_DEPENDENCY_UNJUSTIFIED:{self.path}:{self.line}:"
            f"missing={','.join(self.missing)}:section={self.section}:"
            f"assertion={self.assertion}"
        )


def _repo_rel(path: str) -> str:
    rel = PurePosixPath(path)
    if rel.is_absolute() or ".." in rel.parts:
        raise ValueError(f"RIGID_DEPENDENCY_SURFACE_PATH_INVALID:{path}")
    return rel.as_posix()


def _historical_path(path: str) -> bool:
    pure = PurePosixPath(path)
    return bool(HISTORICAL_PARTS.intersection(part.lower() for part in pure.parts)) or bool(
        HISTORICAL_NAME_RE.search(pure.name)
    )


def _status_from_lines(lines: list[str]) -> str | None:
    for line in lines:
        match = STATUS_LINE_RE.match(line.strip(" `-"))
        if match:
            return match.group(1).strip()
    return None


def _top_level_status(text: str) -> str | None:
    """Read only the document's leading lifecycle, never a nested section."""
    lines = text.splitlines()
    boundary = len(lines)
    for index, line in enumerate(lines):
        # A level-1 title is part of the preamble; a level-2 heading begins a
        # nested section whose STATUS must not classify the whole document.
        if re.match(r"^#{2,6}\s+", line):
            boundary = index
            break
    leading = lines[: min(boundary, 80)]
    # Prefer the first leading machine YAML block when present.
    joined = "\n".join(leading)
    fenced = re.search(r"```ya?ml\s*\n(.*?)```", joined, re.DOTALL | re.IGNORECASE)
    if fenced:
        status = _status_from_lines(fenced.group(1).splitlines())
        if status is not None:
            return status
    return _status_from_lines(leading)


def _section_status(body: str) -> str | None:
    """Read a section-local lifecycle only from its leading machine preamble."""
    return _status_from_lines(body.splitlines()[:20])


def _is_nonlive_status(status: str | None) -> bool:
    return status is not None and NONLIVE_STATUS_RE.match(status.strip()) is not None


def is_historical(path: str, text: str, *, explicitly_selected: bool = False) -> bool:
    if explicitly_selected:
        return False
    return _historical_path(path) or _is_nonlive_status(_top_level_status(text))


def _yaml_block(text: str) -> dict[str, object]:
    """Parse the first simple fenced YAML mapping without importing a policy parser."""
    match = re.search(r"```ya?ml\s*\n(.*?)```", text, re.DOTALL | re.IGNORECASE)
    body = match.group(1) if match else text[:3000]
    result: dict[str, object] = {}
    for line in body.splitlines():
        item = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*?)\s*$", line)
        if item:
            result[item.group(1)] = item.group(2).strip('"\'')
    return result


def _current_task(repo: Path) -> list[Surface]:
    pointer = repo / "docs/Codex/CURRENT.md"
    if not pointer.is_file():
        return []
    row = _yaml_block(pointer.read_text(encoding="utf-8"))
    if str(row.get("status", "")).upper() != "ACTIVE":
        return []
    task = row.get("task_file")
    return [Surface(_repo_rel(str(task)), "markdown")] if task else []


def _selected_goal(repo: Path) -> list[Surface]:
    state = repo / "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json"
    if not state.is_file():
        return []
    data = json.loads(state.read_text(encoding="utf-8"))
    path = data.get("current", {}).get("selected_bus_goal_path")
    return [Surface(_repo_rel(path), "markdown")] if isinstance(path, str) and path else []


def _open_queue_requests(repo: Path) -> list[Surface]:
    queue = repo / "docs/routeB_bus/PROSHKA_QUEUE.md"
    if not queue.is_file():
        return []
    text = queue.read_text(encoding="utf-8")
    blocks = re.split(r"(?m)(?=^##\s+REQ-)", text)
    result: list[Surface] = []
    for block in blocks:
        status = _status_from_lines(block.splitlines()[:30])
        if status is None or re.match(r"(?i)^(?:OPEN|IN_REVIEW)\b", status) is None:
            continue
        request = re.search(r"(?im)^\s*-\s*Request\s*:\s*`([^`]+)`", block)
        if request:
            result.append(Surface(_repo_rel(request.group(1)), "markdown"))
    return result


def discover_surfaces(repo: Path) -> tuple[Surface, ...]:
    surfaces = [Surface(path, "markdown") for path in STATIC_ACTIVE]
    skill_root = repo / ".agents/skills"
    if skill_root.is_dir():
        for path in sorted(skill_root.glob("*/SKILL.md")):
            rel = path.relative_to(repo).as_posix()
            text = path.read_text(encoding="utf-8")
            # A compatibility shim is routing metadata, not a live method body.
            if re.search(r"(?i)compatibility\s+shim", text[:1200]):
                continue
            surfaces.append(Surface(rel, "markdown"))
    surfaces.extend(_current_task(repo))
    surfaces.extend(_selected_goal(repo))
    surfaces.extend(_open_queue_requests(repo))
    surfaces.extend(Surface(path, "generator") for path in NAMED_GENERATORS)
    unique: dict[tuple[str, str], Surface] = {}
    for surface in surfaces:
        if (repo / surface.path).is_file():
            unique[(surface.path, surface.kind)] = surface
    return tuple(unique.values())


def _markdown_sections(text: str) -> Iterable[tuple[str, int, str]]:
    starts = list(
        re.finditer(
            r"(?m)^(?:#{1,6}\s+(.+?)\s*|((?:W|K|P)\d+[A-Z]?\.)\s+(.+?)\s*)$",
            text,
        )
    )
    if not starts:
        yield "document", 1, text
        return
    if starts[0].start() > 0:
        yield "preamble", 1, text[: starts[0].start()]
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        line = text.count("\n", 0, match.start()) + 1
        title = match.group(1) or f"{match.group(2)} {match.group(3)}"
        yield title.strip(), line, text[match.start() : end]


def _generator_sections(text: str) -> Iterable[tuple[str, int, str]]:
    try:
        tree = ast.parse(text)
    except SyntaxError:
        yield "generator", 1, text
        return
    module_strings: list[str] = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            strings = [
                child.value
                for child in ast.walk(node)
                if isinstance(child, ast.Constant) and isinstance(child.value, str)
            ]
            if strings:
                yield node.name, node.lineno, "\n".join(strings)
        elif isinstance(node, ast.Assign):
            module_strings.extend(
                child.value
                for child in ast.walk(node.value)
                if isinstance(child, ast.Constant) and isinstance(child.value, str)
            )
    if module_strings:
        yield "module_constants", 1, "\n".join(module_strings)


def _assertions(section: str) -> list[re.Match[str]]:
    matches = [match for pattern in ASSERTION_PATTERNS for match in pattern.finditer(section)]
    return sorted(matches, key=lambda item: item.start())


def _missing_justification(section: str) -> tuple[str, ...]:
    exemption = EXEMPTION_RE.search(section)
    if exemption and exemption.group(1) in EXEMPTIONS:
        return ()
    return tuple(name for name, pattern in FIELD_PATTERNS.items() if pattern.search(section) is None)


def scan_text(path: str, text: str, *, kind: str = "markdown", explicitly_selected: bool = False) -> list[Finding]:
    if kind == "markdown" and is_historical(path, text, explicitly_selected=explicitly_selected):
        return []
    sections = _generator_sections(text) if kind == "generator" else _markdown_sections(text)
    findings: list[Finding] = []
    for title, base_line, body in sections:
        if kind == "markdown" and _is_nonlive_status(_section_status(body)):
            continue
        missing = _missing_justification(body)
        if not missing:
            continue
        for match in _assertions(body):
            line = base_line + body.count("\n", 0, match.start())
            assertion = " ".join(match.group(0).split())[:160]
            findings.append(Finding(path, line, title, missing, assertion))
    return findings


def scan_repo(repo: Path) -> list[Finding]:
    findings: list[Finding] = []
    dynamic_selected = {surface.path for surface in _current_task(repo) + _selected_goal(repo) + _open_queue_requests(repo)}
    for surface in discover_surfaces(repo):
        text = (repo / surface.path).read_text(encoding="utf-8")
        findings.extend(
            scan_text(
                surface.path,
                text,
                kind=surface.kind,
                explicitly_selected=surface.path in dynamic_selected,
            )
        )
    return findings
