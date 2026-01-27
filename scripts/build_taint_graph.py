#!/usr/bin/env python3
import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle"
Q3_DIR = ROOT / "Q3"
ACTIVE_DIR = ROOT / "ACTIVE"
RISK_MODEL_JSON = ACTIVE_DIR / "RISK_MODEL.json"

IMPORT_RE = re.compile(r"^\s*import\s+(?P<mods>.+)$")
SORRY_RE = re.compile(r"\bsorry\b")


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def load_json(path: Path, default):
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def module_name_for(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def build_module_map(exclude_paths: list[tuple[str, ...]]) -> dict[str, str]:
    mod_map = {}
    for p in Q3_DIR.rglob("*.lean"):
        if should_skip(p, exclude_paths):
            continue
        mod_map[module_name_for(p)] = str(p.relative_to(ROOT))
    return mod_map


def scan_imports(path: Path) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        return []
    mods = []
    for line in text.splitlines():
        m = IMPORT_RE.match(line)
        if not m:
            continue
        # split by whitespace; Lean allows multiple modules per line
        mods.extend(m.group("mods").split())
    return mods


def scan_sorries(path: Path) -> list[int]:
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        return []
    lines = []
    for i, line in enumerate(text.splitlines(), start=1):
        if SORRY_RE.search(line):
            lines.append(i)
    return lines


def should_skip(path: Path, exclude_paths: list[tuple[str, ...]]) -> bool:
    rel_parts = path.relative_to(ROOT).parts
    for ex in exclude_paths:
        if not ex:
            continue
        for i in range(0, len(rel_parts) - len(ex) + 1):
            if tuple(rel_parts[i : i + len(ex)]) == ex:
                return True
    return False


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(ACTIVE_DIR / "TAINT_GRAPH.md"))
    ap.add_argument("--json", default=str(ACTIVE_DIR / "TAINT_GRAPH.json"))
    ap.add_argument("--numeric", default=str(ACTIVE_DIR / "NUMERIC_CHECKS_REPORT.json"))
    ap.add_argument("--risk", default=str(RISK_MODEL_JSON))
    ap.add_argument(
        "--exclude",
        action="append",
        default=["Q3/Clean"],
        help="exclude subpaths (relative to repo root), can repeat",
    )
    args = ap.parse_args()

    exclude_paths = [Path(item).parts for item in args.exclude]

    mod_map = build_module_map(exclude_paths)

    numeric_report = load_json(Path(args.numeric), {})
    numeric_map = {c.get("id"): c for c in numeric_report.get("checks", [])}

    risk_model = load_json(Path(args.risk), {})
    risk_threshold = float(risk_model.get("risk_threshold", 1.0))
    kill_switch = bool(risk_model.get("kill_switch_on_risk", True))
    weights = risk_model.get("weights", {})
    per_sorry = float(weights.get("per_sorry", 0.5))
    numeric_fail = float(weights.get("numeric_fail", 5.0))
    speculative_weight = float(weights.get("speculative", 0.2))
    speculative_files = set(risk_model.get("speculative_files", []))
    intrinsic_overrides = risk_model.get("intrinsic_overrides", {})

    nodes = {}
    for path in sorted(Q3_DIR.rglob("*.lean")):
        if should_skip(path, exclude_paths):
            continue
        rel = path.relative_to(ROOT)
        file_id = str(rel)
        module = module_name_for(path)
        imports = []
        for mod in scan_imports(path):
            if mod in mod_map:
                imports.append(mod_map[mod])

        sorries = scan_sorries(path)
        numeric = numeric_map.get(file_id) or numeric_map.get(module) or {}
        numeric_status = numeric.get("status", "UNKNOWN")

        direct_status = "VERIFIED"
        if numeric_status == "FAIL":
            direct_status = "BROKEN"
        elif sorries:
            direct_status = "SORRY"

        override = intrinsic_overrides.get(file_id)
        if override is None:
            intrinsic_risk = per_sorry * len(sorries)
            if numeric_status == "FAIL":
                intrinsic_risk += numeric_fail
            if file_id in speculative_files:
                intrinsic_risk += speculative_weight
        else:
            intrinsic_risk = float(override)

        nodes[file_id] = {
            "id": file_id,
            "module": module,
            "dependencies": sorted(set(imports)),
            "sorries": sorries,
            "numeric_check": numeric_status,
            "direct_status": direct_status,
            "intrinsic_risk": intrinsic_risk,
            "propagation_status": None,
            "integrity_status": None,
            "taint_source": [],
            "risk_score": None,
            "risk_threshold": risk_threshold,
            "risk_status": None,
            "risk_exceeds": None,
            "is_doomed": None,
        }

    # propagate statuses
    visiting = set()
    memo = {}

    def propagate(fid: str) -> dict:
        if fid in memo:
            return memo[fid]
        if fid in visiting:
            # cycle should not happen; mark as TAINTED to be safe
            node = nodes[fid]
            node["propagation_status"] = "TAINTED"
            node["integrity_status"] = "TAINTED"
            node["risk_score"] = node["intrinsic_risk"]
            node["risk_exceeds"] = node["risk_score"] > risk_threshold
            node["risk_status"] = "EXCESSIVE" if node["risk_exceeds"] else "OK"
            node["is_doomed"] = (node["direct_status"] == "BROKEN") or (
                kill_switch and node["risk_exceeds"]
            )
            memo[fid] = node
            return node
        visiting.add(fid)
        node = nodes[fid]
        dep_nodes = [propagate(dep) for dep in node["dependencies"]]

        # compute risk
        risk_score = node["intrinsic_risk"] + sum(d["risk_score"] for d in dep_nodes)

        # compute propagation status
        direct = node["direct_status"]
        if direct in ("BROKEN", "SORRY"):
            status = direct
            taint_sources = []
        else:
            taint_sources = []
            status = "VERIFIED"
            for dep_node in dep_nodes:
                dep_status = dep_node["propagation_status"]
                if dep_status == "BROKEN":
                    status = "BROKEN"
                    taint_sources.append(dep_node["id"])
                    break
                if dep_status in ("SORRY", "TAINTED"):
                    status = "TAINTED"
                    taint_sources.append(dep_node["id"])

        risk_exceeds = risk_score > risk_threshold
        dep_doomed = any(d.get("is_doomed") for d in dep_nodes)
        is_doomed = (status == "BROKEN") or (kill_switch and (risk_exceeds or dep_doomed))

        node["propagation_status"] = status
        node["integrity_status"] = status
        node["taint_source"] = taint_sources
        node["risk_score"] = round(risk_score, 6)
        node["risk_exceeds"] = risk_exceeds
        node["risk_status"] = "EXCESSIVE" if risk_exceeds else "OK"
        node["is_doomed"] = is_doomed

        memo[fid] = node
        visiting.remove(fid)
        return node

    # drop dependencies that were excluded from the node set
    for node in nodes.values():
        node["dependencies"] = [d for d in node["dependencies"] if d in nodes]

    for fid in list(nodes.keys()):
        propagate(fid)

    data = {
        "generated_at": now_utc(),
        "root": "Q3/",
        "nodes": list(nodes.values()),
    }

    # markdown summary
    counts = {"VERIFIED": 0, "TAINTED": 0, "SORRY": 0, "BROKEN": 0}
    doomed_count = 0
    for n in nodes.values():
        counts[n["propagation_status"]] = counts.get(n["propagation_status"], 0) + 1
        if n.get("is_doomed"):
            doomed_count += 1

    md = []
    md.append(f"# Taint Graph (auto) — {data['generated_at']}")
    md.append("")
    md.append("**Purpose:** Propagate `sorry`/BROKEN status upward across file import graph.")
    md.append("**Source:** Q3 file imports + numeric checks report")
    md.append("")
    md.append("**Counts:** " + ", ".join([f"{k}={v}" for k, v in counts.items()]))
    md.append(f"**Doomed:** {doomed_count}")
    md.append("")

    md.append("## DOOMED")
    for n in sorted(nodes.values(), key=lambda x: x["id"]):
        if n.get("is_doomed"):
            md.append(f"- `{n['id']}`")
    md.append("")

    for status in ("BROKEN", "SORRY", "TAINTED", "VERIFIED"):
        md.append(f"## {status}")
        for n in sorted(nodes.values(), key=lambda x: x["id"]):
            if n["propagation_status"] != status:
                continue
            md.append(f"- `{n['id']}`")
        md.append("")

    Path(args.out).write_text("\n".join(md) + "\n", encoding="utf-8")
    Path(args.json).write_text(json.dumps(data, indent=2), encoding="utf-8")
    print(f"Wrote {args.out} and {args.json}")


if __name__ == "__main__":
    main()
