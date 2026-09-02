#!/usr/bin/env python3
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

try:
    from scripts.qmd_ops import qmd_lock, run_qmd
except ModuleNotFoundError:  # direct execution from scripts/
    from qmd_ops import qmd_lock, run_qmd

ROOT = Path(__file__).resolve().parents[1] / "q3.lean.aristotle"
ACTIVE_DIR = ROOT / "ACTIVE"
PIPELINE_DIR = ACTIVE_DIR / "pipeline"
DEFAULT_CONFIG = PIPELINE_DIR / "RESEARCH_ORACLE.json"
DEFAULT_EQUIV = PIPELINE_DIR / "EQUIVALENCE_GRAPH.json"


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")


def load_json(path: Path, default):
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def save_json(path: Path, data) -> None:
    path.write_text(json.dumps(data, indent=2), encoding="utf-8")


def resolve_qmd(cmd: str) -> str:
    found = shutil.which(cmd)
    if found is not None:
        return found
    bun_qmd = Path.home() / ".bun" / "bin" / "qmd"
    if bun_qmd.exists():
        return str(bun_qmd)
    raise SystemExit(
        f"qmd not found: expected '{cmd}' on PATH. Install via: bun install -g https://github.com/tobi/qmd"
    )


def resolve_default(path: Path, legacy: Path) -> Path:
    if path.exists():
        return path
    if legacy.exists():
        return legacy
    return path


def run(
    cmd: list[str],
    cwd: Path | None = None,
    *,
    qmd_timeout_s: float | None = None,
) -> str:
    if cmd and Path(cmd[0]).name == "qmd":
        try:
            if qmd_timeout_s is None:
                return run_qmd(cmd, cwd=cwd)
            return run_qmd(
                cmd,
                cwd=cwd,
                retries=0,
                timeout_s=qmd_timeout_s,
            )
        except (RuntimeError, TimeoutError) as exc:
            raise SystemExit(str(exc)) from exc
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise SystemExit(proc.stderr.strip() or proc.stdout.strip())
    return proc.stdout


def normalize_results(raw: str) -> list[dict]:
    text = raw.strip()
    if not text or text in {
        "No results found.",
        "No results found above minimum score threshold.",
    }:
        return []
    if not text.startswith("["):
        start = text.find("[")
        end = text.rfind("]")
        if start != -1 and end != -1 and start < end:
            text = text[start : end + 1]
    data = json.loads(text)
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


def build_query_cmd(
    qmd: str,
    mode: str,
    query: str,
    *,
    collection: str,
    limit: int,
    min_score: float,
    index: str | None,
    full: bool,
    line_numbers: bool,
) -> list[str]:
    cmd = [qmd, mode, query, "--json", "-n", str(limit)]
    if collection:
        cmd += ["-c", collection]
    if min_score:
        cmd += ["--min-score", str(min_score)]
    if full:
        cmd += ["--full"]
    if line_numbers:
        cmd += ["--line-numbers"]
    if index:
        cmd += ["--index", index]
    return cmd


def run_query_mode(
    qmd: str,
    mode: str,
    query: str,
    *,
    collection: str,
    limit: int,
    min_score: float,
    index: str | None,
    full: bool,
    line_numbers: bool,
    budget_seconds: float | None = None,
) -> list[dict]:
    cmd = build_query_cmd(
        qmd,
        mode,
        query,
        collection=collection,
        limit=limit,
        min_score=min_score,
        index=index,
        full=full,
        line_numbers=line_numbers,
    )
    lock_timeout = 300.0 if budget_seconds is None else budget_seconds
    with qmd_lock(f"research_oracle_{mode}", timeout_s=lock_timeout):
        raw = run(cmd, qmd_timeout_s=budget_seconds)
    return normalize_results(raw)


def merge_ranked_results(result_sets: dict[str, list[dict]], limit: int) -> list[dict]:
    # Reciprocal-rank fusion is stable across heterogeneous score scales (BM25 vs vectors).
    fused: dict[tuple[str | None, str | None, str | None], dict] = {}
    k = 60.0
    for mode, facts in result_sets.items():
        for rank, fact in enumerate(facts, start=1):
            key = (fact.get("docid"), fact.get("file"), fact.get("snippet"))
            entry = fused.setdefault(
                key,
                {
                    "docid": fact.get("docid"),
                    "file": fact.get("file"),
                    "score": fact.get("score"),
                    "title": fact.get("title"),
                    "context": fact.get("context"),
                    "snippet": fact.get("snippet"),
                    "rrf_score": 0.0,
                    "sources": [],
                },
            )
            if entry.get("score") is None or (
                fact.get("score") is not None and fact.get("score", 0) > entry.get("score", 0)
            ):
                entry["score"] = fact.get("score")
            if not entry.get("title") and fact.get("title"):
                entry["title"] = fact.get("title")
            if not entry.get("context") and fact.get("context"):
                entry["context"] = fact.get("context")
            entry["rrf_score"] += 1.0 / (k + rank)
            entry["sources"].append(mode)

    merged = sorted(
        fused.values(),
        key=lambda item: (
            -item["rrf_score"],
            -(item.get("score") or 0),
            item.get("title") or "",
        ),
    )
    for item in merged:
        item["sources"] = sorted(set(item["sources"]))
    return merged[:limit]


def make_ext_id(docid: str, snippet: str | None) -> str:
    h = hashlib.sha1()
    h.update((docid or "").encode("utf-8"))
    h.update((snippet or "").encode("utf-8"))
    return f"ext_{h.hexdigest()[:10]}"


def cmd_query(args, cfg) -> int:
    qmd = resolve_qmd(cfg.get("qmd_command", "qmd"))
    mode = args.mode
    collection = args.collection or cfg.get("collection", "")
    limit = args.limit or cfg.get("limit", 10)
    min_score = args.min_score if args.min_score is not None else cfg.get("min_score", 0)
    index = args.index or cfg.get("index")

    if mode == "query":
        per_backend = max(limit, 8)
        result_sets: dict[str, list[dict]] = {}
        backend_errors: list[str] = []
        for backend in ("search", "vsearch"):
            try:
                backend_budget = (
                    args.budget_seconds
                    if args.budget_seconds is not None
                    else (3.0 if backend == "search" else 15.0)
                )
                result_sets[backend] = run_query_mode(
                    qmd,
                    backend,
                    args.query,
                    collection=collection,
                    limit=per_backend,
                    min_score=min_score,
                    index=index,
                    full=args.full,
                    line_numbers=args.line_numbers,
                    budget_seconds=backend_budget,
                )
            except SystemExit as exc:
                backend_errors.append(f"{backend}: {exc}")

        if not result_sets:
            raise SystemExit(
                "hybrid query failed for both backends:\n" + "\n".join(backend_errors)
            )

        for message in backend_errors:
            print(f"[research_oracle] degraded backend: {message}", file=sys.stderr)
        facts = merge_ranked_results(result_sets, limit)
    else:
        qmd_mode = "query" if mode == "qmd-query" else mode
        try:
            mode_budget = (
                args.budget_seconds
                if args.budget_seconds is not None
                else (15.0 if qmd_mode == "vsearch" else 3.0)
            )
            facts = run_query_mode(
                qmd,
                qmd_mode,
                args.query,
                collection=collection,
                limit=limit,
                min_score=min_score,
                index=index,
                full=args.full,
                line_numbers=args.line_numbers,
                budget_seconds=mode_budget,
            )
        except TimeoutError as exc:
            raise SystemExit(str(exc)) from exc

    if args.raw:
        print(json.dumps(facts, indent=2))
    else:
        print(json.dumps(facts, indent=2))

    if args.out:
        Path(args.out).write_text(json.dumps(facts, indent=2), encoding="utf-8")
    return 0


def cmd_ingest(args, cfg) -> int:
    qmd = resolve_qmd(cfg.get("qmd_command", "qmd"))
    collection = args.collection or cfg.get("collection", "math_papers")
    literature_dir = args.path or cfg.get("literature_dir", "literature")
    context = args.context or cfg.get("context", "")

    try:
        with qmd_lock("research_oracle_ingest"):
            cmd = [qmd, "collection", "add", literature_dir, "--name", collection]
            run(cmd)
            if context:
                run([qmd, "context", "add", f"qmd://{collection}", context])
            if args.embed:
                run([qmd, "embed"])
    except TimeoutError as exc:
        raise SystemExit(str(exc)) from exc
    return 0


def cmd_add_speculative(args, cfg) -> int:
    qmd = resolve_qmd(cfg.get("qmd_command", "qmd"))
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

    try:
        with qmd_lock("research_oracle_add_speculative"):
            raw = run(cmd)
    except TimeoutError as exc:
        raise SystemExit(str(exc)) from exc
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


def cmd_validate_external_receipt(args, _cfg) -> int:
    """Validate a supplied external receipt without launching another search."""
    try:
        from scripts import search_external_lean
    except ModuleNotFoundError:
        import search_external_lean  # type: ignore[no-redef]

    payload, errors = search_external_lean.load_secure_receipt(
        Path(args.receipt), expected_query=args.query
    )
    if errors or payload is None:
        print(
            json.dumps(
                {
                    "schema": search_external_lean.SCHEMA,
                    "query": args.query,
                    "errors": errors,
                    "boundary": search_external_lean.INCOMPLETE_BOUNDARY,
                },
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
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
    p_query.add_argument(
        "--mode",
        default="query",
        choices=["query", "search", "vsearch", "qmd-query"],
    )
    p_query.add_argument("-n", "--limit", type=int)
    p_query.add_argument("--min-score", type=float)
    p_query.add_argument("-c", "--collection")
    p_query.add_argument("--index")
    p_query.add_argument("--full", action="store_true")
    p_query.add_argument("--line-numbers", action="store_true")
    p_query.add_argument("--raw", action="store_true", help="print raw qmd JSON")
    p_query.add_argument("--out", help="write parsed results to file")
    p_query.add_argument(
        "--budget-seconds",
        type=float,
        help="separate lock and command budget; query retries are always zero",
    )
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

    p_receipt = sub.add_parser("validate-external-receipt")
    p_receipt.add_argument("query")
    p_receipt.add_argument("receipt")
    p_receipt.set_defaults(func=cmd_validate_external_receipt)

    args = ap.parse_args()
    cfg_path = resolve_default(Path(args.config), ACTIVE_DIR / "RESEARCH_ORACLE.json")
    cfg = load_json(cfg_path, {})
    return args.func(args, cfg)


if __name__ == "__main__":
    raise SystemExit(main())
