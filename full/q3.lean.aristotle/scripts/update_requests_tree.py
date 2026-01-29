#!/usr/bin/env python3
"""Update ACTIVE/requests node files with related outputs.

Heuristic: derive a match key from the request filename, then attach any
ACTIVE/output files whose stem contains that key.
"""

import re
from pathlib import Path

ROOT = Path("/Users/emalam/Documents/GitHub/chen_q3/sandboxes/projekt_2/full/q3.lean.aristotle")
ACTIVE = ROOT / "ACTIVE"
REQUESTS_DIR = ACTIVE / "requests"
OUTPUT_DIR = ACTIVE / "output"

REQUEST_RE = re.compile(r"^- request: `(?P<path>[^`]+)`", re.M)
RELATED_RE = re.compile(r"^- related outputs:.*$", re.M)

# Strip trailing request/date markers to build a matching key
REQUEST_SUFFIX_RE = re.compile(r"(_request(_strict)?(_\d{4}_\d{2}_\d{2})?)$")


def request_match_keys(stem: str) -> list[str]:
    base = REQUEST_SUFFIX_RE.sub("", stem)
    base = base.replace("__", "_")
    keys = [base]
    for prefix in ("proshka_", "aristotle_"):
        if base.startswith(prefix):
            keys.append(base[len(prefix) :])
    return [k for k in keys if k]


def list_outputs() -> list[Path]:
    if not OUTPUT_DIR.exists():
        return []
    return sorted(p for p in OUTPUT_DIR.iterdir() if p.is_file())


def related_outputs_for(keys: list[str], outputs: list[Path]) -> list[Path]:
    keys_l = [k.lower() for k in keys if k]
    matches = []
    for p in outputs:
        stem_l = p.stem.lower()
        hit = False
        for key_l in keys_l:
            if key_l in stem_l:
                hit = True
                break
            # Fallback: all tokens from key appear somewhere in stem
            tokens = [t for t in key_l.split("_") if t]
            if tokens and all(tok in stem_l for tok in tokens):
                hit = True
                break
        if hit:
            matches.append(p)
    return matches


def rel_to_node(node_path: Path, target: Path) -> str:
    rel = Path("..") / ".." / "output" / target.name
    return rel.as_posix()


def update_node(node_path: Path, outputs: list[Path]) -> bool:
    text = node_path.read_text(encoding="utf-8")
    m = REQUEST_RE.search(text)
    if not m:
        return False
    req_rel = m.group("path")
    req_path = (node_path.parent / req_rel).resolve()
    if not req_path.exists():
        return False
    keys = request_match_keys(req_path.stem)
    matches = related_outputs_for(keys, outputs)
    if matches:
        lines = ["- related outputs:"]
        for p in matches:
            lines.append(f"  - `{rel_to_node(node_path, p)}`")
        related_block = "\n".join(lines)
    else:
        related_block = "- related outputs: (none linked)"

    if RELATED_RE.search(text):
        new_text = RELATED_RE.sub(related_block, text)
    else:
        # If missing, append under Source section
        new_text = text.replace("## Source\n", f"## Source\n{related_block}\n", 1)

    if new_text != text:
        node_path.write_text(new_text, encoding="utf-8")
        return True
    return False


def main() -> None:
    outputs = list_outputs()
    if not REQUESTS_DIR.exists():
        raise SystemExit(f"Missing requests dir: {REQUESTS_DIR}")
    updated = 0
    for node in REQUESTS_DIR.rglob("node.md"):
        if update_node(node, outputs):
            updated += 1
    print(f"Updated {updated} nodes")


if __name__ == "__main__":
    main()
