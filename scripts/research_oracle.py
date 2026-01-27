#!/usr/bin/env python3
import argparse
import hashlib
import json
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "full" / "q3.lean.aristotle"
ACTIVE_DIR = ROOT / "ACTIVE"
DEFAULT_CONFIG = ACTIVE_DIR / "RESEARCH_ORACLE.json"
DEFAULT_EQUIV = ACTIVE_DIR / "EQUIVALENCE_GRAPH.json"


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def load_json(path: Path, default):
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def save_json(path: Path, data) -> None:
    path.write_text(json.dumps(data, indent=2), encoding="utf-8")


def require_qmd(cmd: str) -> None:
    if shutil.which(cmd) is None:
        raise SystemExit(
            f"qmd not found: expected '{cmd}' on PATH. Install via: bun install -g https://github.com/tobi/qmd"
        )


def run(cmd: list[str], cwd: Path | None = None) -> str:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise SystemExit(proc.stderr.strip() or proc.stdout.strip())
    return proc.stdout


def normalize_results(raw: str) -> list[dict]:
    data = json.loads(raw)
    facts = []
    for item in data:
        facts.append(
            {
                "docid": item.get("docid"),
                "file": item.get("file"),
                "score": item.get("score"),
                "title": item.get("title"),
                "context": item.get("context"),
                "snippet": item.get("snippet") or item.get("body"),
            }
        )
    return facts


def make_ext_id(docid: str, snippet: str | None) -> str:
    h = hashlib.sha1()
    h.update((docid or "").encode("utf-8"))
    h.update((snippet or "").encode("utf-8"))
    return f"ext_{h.hexdigest()[:10]}"


def cmd_query(args, cfg) -> int:
    qmd = cfg.get("qmd_command", "qmd")
    require_qmd(qmd)
    mode = args.mode
    collection = args.collection or cfg.get("collection", "")
    limit = args.limit or cfg.get("limit", 10)
    min_score = args.min_score if args.min_score is not None else cfg.get("min_score", 0)
    index = args.index or cfg.get("index")

    cmd = [qmd, mode, args.query, "--json", "-n", str(limit)]
    if collection:
        cmd += ["-c", collection]
    if min_score:
        cmd += ["--min-score", str(min_score)]
    if args.full:
        cmd += ["--full"]
    if args.line_numbers:
        cmd += ["--line-numbers"]
    if index:
        cmd += ["--index", index]

    raw = run(cmd)
    facts = normalize_results(raw)

    if args.raw:
        print(raw)
    else:
        print(json.dumps(facts, indent=2))

    if args.out:
        Path(args.out).write_text(json.dumps(facts, indent=2), encoding="utf-8")
    return 0


def cmd_ingest(args, cfg) -> int:
    qmd = cfg.get("qmd_command", "qmd")
    require_qmd(qmd)
    collection = args.collection or cfg.get("collection", "math_papers")
    literature_dir = args.path or cfg.get("literature_dir", "literature")
    context = args.context or cfg.get("context", "")

    cmd = [qmd, "collection", "add", literature_dir, "--name", collection]
    run(cmd)
    if context:
        run([qmd, "context", "add", f"qmd://{collection}", context])
    if args.embed:
        run([qmd, "embed"])
    return 0


def cmd_add_speculative(args, cfg) -> int:
    qmd = cfg.get("qmd_command", "qmd")
    require_qmd(qmd)
    collection = args.collection or cfg.get("collection", "")
    limit = args.limit or cfg.get("limit", 10)
    min_score = args.min_score if args.min_score is not None else cfg.get("min_score", 0)
    index = args.index or cfg.get("index")

    cmd = [qmd, args.mode, args.query, "--json", "-n", str(limit)]
    if collection:
        cmd += ["-c", collection]
    if min_score:
        cmd += ["--min-score", str(min_score)]
    if index:
        cmd += ["--index", index]

    raw = run(cmd)
    facts = normalize_results(raw)
    top_k = args.top_k or min(3, len(facts))
    selected = facts[:top_k]

    equiv_path = Path(args.equiv or DEFAULT_EQUIV)
    equiv = load_json(equiv_path, {"nodes": [], "edges": []})

    new_nodes = []
    new_edges = []
    for fact in selected:
        ext_id = make_ext_id(fact.get("docid") or "", fact.get("snippet"))
        node = {
            "id": ext_id,
            "type": "external_claim",
            "status": "speculative",
            "title": fact.get("title"),
            "snippet": fact.get("snippet"),
            "source": {
                "qmd_docid": fact.get("docid"),
                "file": fact.get("file"),
                "score": fact.get("score"),
                "collection": collection,
                "query": args.query,
            },
        }
        new_nodes.append(node)
        if args.target:
            new_edges.append(
                {
                    "source": ext_id,
                    "target": args.target,
                    "type": "cites",
                    "status": "speculative",
                    "notes": args.notes or "",
                }
            )

    existing_ids = {n.get("id") for n in equiv.get("nodes", [])}
    equiv["nodes"] = equiv.get("nodes", []) + [n for n in new_nodes if n["id"] not in existing_ids]
    equiv["edges"] = equiv.get("edges", []) + new_edges
    equiv["generated_at"] = now_utc()

    if args.dry_run:
        print(json.dumps({"nodes": new_nodes, "edges": new_edges}, indent=2))
        return 0

    save_json(equiv_path, equiv)
    print(f"Wrote {equiv_path}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", default=str(DEFAULT_CONFIG))
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_ingest = sub.add_parser("ingest")
    p_ingest.add_argument("--path", help="literature directory")
    p_ingest.add_argument("--collection", help="qmd collection name")
    p_ingest.add_argument("--context", help="context string")
    p_ingest.add_argument("--embed", action="store_true", help="run qmd embed after ingest")
    p_ingest.set_defaults(func=cmd_ingest)

    p_query = sub.add_parser("query")
    p_query.add_argument("query")
    p_query.add_argument("--mode", default="query", choices=["query", "search", "vsearch"])
    p_query.add_argument("-n", "--limit", type=int)
    p_query.add_argument("--min-score", type=float)
    p_query.add_argument("-c", "--collection")
    p_query.add_argument("--index")
    p_query.add_argument("--full", action="store_true")
    p_query.add_argument("--line-numbers", action="store_true")
    p_query.add_argument("--raw", action="store_true", help="print raw qmd JSON")
    p_query.add_argument("--out", help="write parsed results to file")
    p_query.set_defaults(func=cmd_query)

    p_add = sub.add_parser("add-speculative")
    p_add.add_argument("query")
    p_add.add_argument("--mode", default="query", choices=["query", "search", "vsearch"])
    p_add.add_argument("-n", "--limit", type=int)
    p_add.add_argument("--top-k", type=int, help="number of results to add")
    p_add.add_argument("--min-score", type=float)
    p_add.add_argument("-c", "--collection")
    p_add.add_argument("--index")
    p_add.add_argument("--target", help="Lean decl or node id to cite")
    p_add.add_argument("--notes", help="edge notes")
    p_add.add_argument("--equiv", help="path to EQUIVALENCE_GRAPH.json")
    p_add.add_argument("--dry-run", action="store_true")
    p_add.set_defaults(func=cmd_add_speculative)

    args = ap.parse_args()
    cfg = load_json(Path(args.config), {})
    return args.func(args, cfg)


if __name__ == "__main__":
    raise SystemExit(main())
