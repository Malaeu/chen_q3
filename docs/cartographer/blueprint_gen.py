#!/usr/bin/env python3
"""Generate an honest leanblueprint skeleton from assembly and proof receipts.

One model produces the Markdown dashboard and the TeX blueprint. An assembly
row is green only when READY is backed by one exact proven proof-registry row
and by the matching public, safe declaration in the Route-B environment dump.
Validation, open mathematics, and unresolved READY receipts remain non-green.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import re
import sqlite3
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path
from typing import Mapping, Sequence

ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = ROOT / "q3.lean.aristotle"
KB_PATH = LEAN_ROOT / "aristotle_db" / "knowledge.db"
PDB_PATH = LEAN_ROOT / "aristotle_db" / "aristotle_proofs.db"
ENV_PATH = ROOT / "docs/cartographer/lean_env/env_index.jsonl"
ENV_DUMP = ROOT / "docs/cartographer/lean_env/envdump.py"
ENV_RECEIPT_PATH = LEAN_ROOT / ".qmd_cache/routeb_env_index_receipt.json"
PREVIEW_PATH = ROOT / "full/blueprint/blueprint.md"
BP_ROOT = LEAN_ROOT / "blueprint"
SRC = BP_ROOT / "src"
MANIFEST_PATH = BP_ROOT / "blueprint_manifest.json"

SCHEMA = "q3_blueprint.v1"
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
ENV_FIELDS = frozenset(
    {
        "name", "kind", "type", "levelParams", "numBinders", "file", "line",
        "doc", "typeConsts", "axioms", "isPrivate", "isUnsafe",
    }
)
TRACKED_INPUTS = (
    "q3.lean.aristotle/aristotle_db/knowledge.db",
    "q3.lean.aristotle/aristotle_db/aristotle_proofs.db",
    "q3.lean.aristotle/Q3/Basic/Defs.lean",
    "q3.lean.aristotle/Q3/Proofs/RouteB",
)
ENV_SOURCE_INPUTS = (
    LEAN_ROOT / "lean-toolchain",
    LEAN_ROOT / "lakefile.toml",
    ENV_DUMP,
)
CHAIN_TITLES = {
    "PSD_CERTIFICATE_FOR_CCM_CELL": "Pillar G2 — finite-cell validation package",
    "SIMPLE_EVEN_GROUND_TO_REAL_ZEROS": "Pillar G3 — real-zeros bridge",
    "G3_CVS_PORT": "Pillar G3 — de Branges/CvS port",
    "G5_CRITICAL_MOMENT": "Pillar G5 — critical-moment budget",
    "GOAL057_CONTINUUM_NUMERATOR_BRIDGE": "Pillar G6 — continuum numerator and edge",
    "REALZERO_GROUND_DIAGONAL_TO_XI": "Goal 058 — ground diagonal to centered Xi",
}


class BlueprintError(RuntimeError):
    """The current sources cannot support an honest generated blueprint."""


def routeb_source_closure() -> list[Path]:
    pending = list((LEAN_ROOT / "Q3/Proofs/RouteB").glob("*.lean"))
    seen: set[Path] = set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for module in re.findall(
            r"^import\s+(Q3(?:\.[A-Za-z0-9_']+)*)\s*$",
            path.read_text(encoding="utf-8"),
            re.MULTILINE,
        ):
            dependency = LEAN_ROOT / (module.replace(".", "/") + ".lean")
            if not dependency.is_file():
                raise BlueprintError(f"local import source missing: {module}")
            pending.append(dependency)
    return sorted(seen)


def routeb_env_source_fingerprint() -> dict[str, str]:
    paths = [*ENV_SOURCE_INPUTS, *routeb_source_closure()]
    return {
        path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in paths
    }


def env_receipt_matches() -> bool:
    if not ENV_PATH.is_file() or not ENV_RECEIPT_PATH.is_file():
        return False
    try:
        receipt = json.loads(ENV_RECEIPT_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return receipt == {
        "schema": "q3_routeb_env_index_receipt.v1",
        "inputs": routeb_env_source_fingerprint(),
        "env_index_sha256": hashlib.sha256(ENV_PATH.read_bytes()).hexdigest(),
    }


def prepare_env_index() -> None:
    if env_receipt_matches():
        print("Route-B EnvDump current: source fingerprint unchanged")
        return
    build = subprocess.run(
        ["lake", "query", "Q3"],
        cwd=LEAN_ROOT,
        capture_output=True,
        text=True,
    )
    if build.returncode != 0:
        diagnostics = "\n".join(
            [*build.stdout.splitlines()[-20:], *build.stderr.splitlines()[-20:]]
        )
        raise BlueprintError(
            f"Route-B library build failed: {build.returncode}\n{diagnostics}"
        )
    print("Route-B library build current")
    environment = os.environ.copy()
    environment.pop("LD_LIBRARY_PATH", None)
    dump = subprocess.run([sys.executable, str(ENV_DUMP)], cwd=ROOT, env=environment)
    if dump.returncode != 0 or not ENV_PATH.is_file():
        raise BlueprintError(f"Route-B EnvDump failed: {dump.returncode}")
    receipt = {
        "schema": "q3_routeb_env_index_receipt.v1",
        "inputs": routeb_env_source_fingerprint(),
        "env_index_sha256": hashlib.sha256(ENV_PATH.read_bytes()).hexdigest(),
    }
    ENV_RECEIPT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=ENV_RECEIPT_PATH.parent, delete=False
    ) as handle:
        json.dump(receipt, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
        temporary = Path(handle.name)
    os.replace(temporary, ENV_RECEIPT_PATH)


@dataclasses.dataclass(frozen=True)
class AssemblyRow:
    chain: str
    step: int
    requirement: str
    required_by: str | None
    supplied_by: str | None
    supplier_file: str | None
    supplier_line: int | None
    status: str
    note: str | None
    objects: str | None

    @property
    def identity(self) -> tuple[str, int, str]:
        return self.chain, self.step, self.requirement


@dataclasses.dataclass(frozen=True)
class ProofRow:
    lemma_id: str
    name: str
    status: str
    statement: str | None
    doc_path: str


@dataclasses.dataclass(frozen=True)
class Receipt:
    proof: ProofRow
    full_name: str
    module: str
    axioms: tuple[str, ...]


@dataclasses.dataclass(frozen=True)
class Node:
    row: AssemblyRow
    publication_status: str
    receipt: Receipt | None
    reason: str

    @property
    def label(self) -> str:
        payload = json.dumps(self.row.identity, ensure_ascii=False, separators=(",", ":"))
        suffix = hashlib.sha256(payload.encode()).hexdigest()[:12]
        stem = re.sub(r"[^A-Za-z0-9]+", "-", self.row.chain).strip("-").lower()
        return f"assembly:{stem}-{self.row.step}-{suffix}"


@dataclasses.dataclass(frozen=True)
class Model:
    nodes: tuple[Node, ...]
    interfaces: tuple[Receipt, ...]
    assembly_rows_digest: str
    proof_statement_digest: str
    env_index_digest: str
    generator_digest: str
    git_head: str

    @property
    def counts(self) -> dict[str, int]:
        result = {
            "assembly_rows": len(self.nodes),
            "green": 0,
            "validation_only": 0,
            "open_math": 0,
            "unresolved_receipt": 0,
            "interface_green": len(self.interfaces),
        }
        keys = {
            "GREEN": "green",
            "VALIDATION_ONLY": "validation_only",
            "OPEN_MATH": "open_math",
            "READY_WITHOUT_EXACT_DECLARATION_RECEIPT": "unresolved_receipt",
        }
        for node in self.nodes:
            result[keys[node.publication_status]] += 1
        return result


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_bytes(value: object) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()


def connect_ro(path: Path) -> sqlite3.Connection:
    if not path.is_file():
        raise BlueprintError(f"missing database: {path}")
    conn = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    conn.row_factory = sqlite3.Row
    return conn


def load_assembly(path: Path = KB_PATH) -> tuple[AssemblyRow, ...]:
    with connect_ro(path) as conn:
        rows = conn.execute(
            "SELECT chain,step,requirement,required_by,supplied_by,supplier_file,"
            "supplier_line,status,note,objects FROM assembly "
            "ORDER BY chain,step,requirement"
        ).fetchall()
    if not rows:
        raise BlueprintError("assembly is empty")
    result = tuple(AssemblyRow(**dict(row)) for row in rows)
    if len({row.identity for row in result}) != len(result):
        raise BlueprintError("duplicate assembly identity")
    return result


def load_proofs(path: Path = PDB_PATH) -> tuple[ProofRow, ...]:
    with connect_ro(path) as conn:
        rows = conn.execute(
            "SELECT l.lemma_id,l.name,l.status,l.statement,d.path AS doc_path "
            "FROM lemmas l JOIN docs d ON d.doc_id=l.doc_id ORDER BY l.lemma_id"
        ).fetchall()
    if not rows:
        raise BlueprintError("proof registry is empty")
    return tuple(ProofRow(**dict(row)) for row in rows)


def load_env(path: Path = ENV_PATH) -> tuple[dict[str, dict], bytes]:
    if not path.is_file():
        raise BlueprintError(
            f"missing {path}; run env -u LD_LIBRARY_PATH python3 "
            "docs/cartographer/lean_env/envdump.py"
        )
    raw = path.read_bytes()
    records: dict[str, dict] = {}
    for line_no, line in enumerate(raw.decode().splitlines(), 1):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as exc:
            raise BlueprintError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
        if not isinstance(record, dict):
            raise BlueprintError(f"{path}:{line_no}: record is not an object")
        missing = ENV_FIELDS - record.keys()
        if missing:
            raise BlueprintError(
                f"{path}:{line_no}: missing fields {', '.join(sorted(missing))}"
            )
        name = record.get("name")
        if not isinstance(name, str) or not name:
            raise BlueprintError(f"{path}:{line_no}: empty declaration name")
        if name in records:
            raise BlueprintError(f"{path}:{line_no}: duplicate declaration {name}")
        if not isinstance(record.get("axioms"), list):
            raise BlueprintError(f"{path}:{line_no}: axioms is not a list")
        records[name] = record
    if not records:
        raise BlueprintError(f"{path}: no declarations")
    return records, raw


def normalize_path(path: str) -> str:
    prefix = "q3.lean.aristotle/"
    return path[len(prefix):] if path.startswith(prefix) else path


def module_for(path: str) -> str:
    normalized = normalize_path(path)
    if not normalized.startswith("Q3/Proofs/RouteB/") or not normalized.endswith(".lean"):
        raise BlueprintError(f"not a Route-B Lean source: {path}")
    return normalized.removesuffix(".lean").replace("/", ".")


def resolve_receipt(
    name: str,
    expected_file: str,
    proofs_by_name: Mapping[str, Sequence[ProofRow]],
    env: Mapping[str, dict],
    env_mtime: float,
    root: Path = ROOT,
) -> Receipt | None:
    """Return None only for true absence; contradictory receipts fail closed."""
    matches = tuple(proofs_by_name.get(name, ()))
    if not matches:
        return None
    if len(matches) != 1:
        raise BlueprintError(f"duplicate proof-registry name: {name}")
    proof = matches[0]
    if proof.status != "proven":
        raise BlueprintError(f"{name}: status {proof.status!r}, not proven")
    if proof.statement is None or not proof.statement.strip():
        raise BlueprintError(f"{name}: empty statement")
    if "\\end{verbatim}" in proof.statement or "\\end{Verbatim}" in proof.statement:
        raise BlueprintError(f"{name}: statement terminates verbatim")
    expected = normalize_path(expected_file)
    if proof.doc_path != expected:
        raise BlueprintError(
            f"{name}: proof path {proof.doc_path!r} != assembly path {expected!r}"
        )
    module = module_for(proof.doc_path)
    candidates = [
        rec for full, rec in env.items()
        if rec.get("file") == module and (full == name or full.endswith(f".{name}"))
    ]
    if len(candidates) != 1:
        raise BlueprintError(
            f"{name}: expected one declaration in {module}, found {len(candidates)}"
        )
    record = candidates[0]
    full_name = str(record["name"])
    source = root / "q3.lean.aristotle" / proof.doc_path
    if not source.is_file():
        raise BlueprintError(f"{name}: source missing: {source}")
    if source.stat().st_mtime > env_mtime:
        raise BlueprintError(f"{name}: source is newer than env_index")
    if record.get("isPrivate") is not False:
        raise BlueprintError(f"{full_name}: private declaration")
    if record.get("isUnsafe") is not False:
        raise BlueprintError(f"{full_name}: unsafe declaration")
    axioms = tuple(sorted(str(item) for item in record["axioms"]))
    unexpected = set(axioms) - STANDARD_AXIOMS
    if unexpected:
        raise BlueprintError(f"{full_name}: nonstandard axioms {sorted(unexpected)}")
    return Receipt(proof, full_name, module, axioms)


def proof_index(proofs: Sequence[ProofRow]) -> dict[str, list[ProofRow]]:
    result: dict[str, list[ProofRow]] = defaultdict(list)
    for proof in proofs:
        result[proof.name].append(proof)
    return result


def classify(
    assembly: Sequence[AssemblyRow],
    proofs: Sequence[ProofRow],
    env: Mapping[str, dict],
    env_mtime: float,
    root: Path = ROOT,
) -> tuple[Node, ...]:
    by_name = proof_index(proofs)
    nodes = []
    for row in assembly:
        if row.status == "VALIDATION":
            nodes.append(Node(row, "VALIDATION_ONLY", None, "not a Lean proof authority"))
        elif row.status != "READY":
            nodes.append(Node(row, "OPEN_MATH", None, f"assembly status {row.status}"))
        elif not row.supplied_by or not row.supplier_file:
            nodes.append(
                Node(
                    row, "READY_WITHOUT_EXACT_DECLARATION_RECEIPT", None,
                    "READY has no exact supplier name and source path",
                )
            )
        else:
            receipt = resolve_receipt(
                row.supplied_by.strip(), row.supplier_file.strip(), by_name,
                env, env_mtime, root,
            )
            if receipt is None:
                nodes.append(
                    Node(
                        row, "READY_WITHOUT_EXACT_DECLARATION_RECEIPT", None,
                        "no unique exact name in aristotle_proofs.db",
                    )
                )
            else:
                nodes.append(Node(row, "GREEN", receipt, "exact proven receipt"))
    return tuple(nodes)


def load_interfaces(
    proofs: Sequence[ProofRow],
    env: Mapping[str, dict],
    env_mtime: float,
    root: Path = ROOT,
) -> tuple[Receipt, ...]:
    by_name = proof_index(proofs)
    required = (
        ("rh_iff_centeredXi_zeros_real",
         "q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean"),
        ("rh_of_canonical_strip_slots",
         "q3.lean.aristotle/Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean"),
    )
    result = []
    for name, path in required:
        receipt = resolve_receipt(name, path, by_name, env, env_mtime, root)
        if receipt is None:
            raise BlueprintError(f"missing interface receipt: {name}")
        result.append(receipt)
    return tuple(result)


def tracked_input_head(root: Path = ROOT) -> str:
    proc = subprocess.run(
        ["git", "log", "-1", "--format=%H", "--", *TRACKED_INPUTS],
        cwd=root, capture_output=True, text=True, check=False,
    )
    head = proc.stdout.strip()
    if proc.returncode or not re.fullmatch(r"[0-9a-f]{40}", head):
        raise BlueprintError(f"cannot resolve input commit: {proc.stderr.strip()}")
    return head


def build_model(
    kb: Path = KB_PATH,
    pdb: Path = PDB_PATH,
    env_path: Path = ENV_PATH,
    root: Path = ROOT,
    generator: Path | None = None,
) -> Model:
    assembly = load_assembly(kb)
    proofs = load_proofs(pdb)
    env, env_raw = load_env(env_path)
    env_mtime = env_path.stat().st_mtime
    generator = generator or Path(__file__).resolve()
    return Model(
        classify(assembly, proofs, env, env_mtime, root),
        load_interfaces(proofs, env, env_mtime, root),
        digest(canonical_bytes([dataclasses.asdict(row) for row in assembly])),
        digest(canonical_bytes([dataclasses.asdict(row) for row in proofs])),
        digest(env_raw),
        digest(generator.read_bytes()),
        tracked_input_head(root),
    )


def tex_escape(text: str) -> str:
    table = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
        "#": r"\#", "_": r"\_\allowbreak{}", "{": r"\{", "}": r"\}",
        "/": r"/\allowbreak{}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
    }
    return "".join(table.get(char, char) for char in text)


def verbatim(statement: str) -> str:
    if "\\end{verbatim}" in statement or "\\end{Verbatim}" in statement:
        raise BlueprintError("statement terminates verbatim")
    newline = "" if statement.endswith("\n") else "\n"
    return (
        "\\mbox{}\\par\\smallskip\n"
        "\\begin{Verbatim}[breaklines=true,breakanywhere=true,fontsize=\\small]\n"
        + statement + newline + "\\end{Verbatim}\n"
        "\\smallskip\n"
    )


def render_node(node: Node) -> str:
    row = node.row
    environment = "validation" if node.publication_status == "VALIDATION_ONLY" else "lemma"
    lines = [
        f"\\begin{{{environment}}}[{tex_escape(row.chain)} / step {row.step}]"
        f"\\label{{{node.label}}}"
    ]
    if node.receipt:
        lines += [f"\\lean{{{node.receipt.full_name}}}", "\\leanok"]
    else:
        lines.append("\\notready")
    lines += [
        f"\\textbf{{Publication state:}} "
        f"\\texttt{{{tex_escape(node.publication_status)}}}.\\par",
        tex_escape(row.requirement) + "\\par",
    ]
    if row.supplied_by:
        lines.append(
            "\\textbf{Assembly supplier field:} "
            f"\\texttt{{{tex_escape(row.supplied_by)}}}.\\par"
        )
    if node.receipt:
        lines.append(verbatim(node.receipt.proof.statement or "").rstrip("\n"))
    else:
        lines.append(f"\\textbf{{Open receipt:}} {tex_escape(node.reason)}.\\par")
        if row.note:
            lines.append(f"\\textbf{{Recorded note:}} {tex_escape(row.note)}\\par")
    lines.append(f"\\end{{{environment}}}")
    if node.receipt:
        lines += [
            "\\begin{proof}", "\\leanok",
            "The proof term is checked in the declaration named above. "
            "This receipt does not strengthen its statement.",
            "\\end{proof}",
        ]
    return "\n".join(lines)


def render_content(model: Model) -> str:
    bridge, roof = model.interfaces
    lines = [
        "% Generated by docs/cartographer/blueprint_gen.py. DO NOT EDIT.",
        "% PX_RH_CLAIM: NOT_MADE",
        r"\section{Definitions and faithfulness interface}",
        r"\textbf{Route status: CHALLENGER / NOT\_RH.}\par",
        r"\textbf{PX\_RH\_CLAIM: NOT\_MADE.}\par",
        (
            r"The project proposition \texttt{Q3.RH} is the classical open-strip "
            r"Riemann Hypothesis over Mathlib's \texttt{riemannZeta}: every zero "
            r"with real part strictly between zero and one has real part one half."
        ),
        r"\begin{definition}[Project RH proposition]\label{def:q3-rh}",
        r"\lean{Q3.RH}",
        r"\texttt{Q3.RH} is defined in \texttt{Q3/Basic/Defs.lean}. "
        r"This records definition identity and does not assert a proof.",
        r"\end{definition}",
        r"\begin{theorem}[Centered-Xi faithfulness bridge]\label{thm:rh-centered-xi}",
        f"\\lean{{{bridge.full_name}}}", r"\leanok",
        verbatim(bridge.proof.statement or "").rstrip("\n"),
        r"\end{theorem}",
        r"\begin{proof}\leanok The proof term is checked by Lean.\end{proof}",
        "This equivalence of formulations is not a proof of either side.",
        r"\section{Conditional roof}",
        r"\begin{theorem}[Canonical strip-slot assembly]\label{thm:conditional-roof}",
        f"\\lean{{{roof.full_name}}}", r"\leanok",
        verbatim(roof.proof.statement or "").rstrip("\n"),
        r"\end{theorem}",
        r"\begin{proof}\leanok The proof term is checked by Lean.\end{proof}",
        "The conclusion is conditional on every named hypothesis in the statement.",
    ]
    grouped: dict[str, list[Node]] = defaultdict(list)
    for node in model.nodes:
        grouped[node.row.chain].append(node)
    for chain in sorted(grouped):
        lines += ["", f"\\section{{{tex_escape(CHAIN_TITLES.get(chain, chain))}}}"]
        for node in grouped[chain]:
            lines += ["", render_node(node)]
    lines += [
        "", r"\section{Bibliography}", r"\nocite{*}", r"\bibliographystyle{plain}",
        r"\bibliography{references}", "",
    ]
    return "\n".join(lines)


def render_preview(model: Model) -> str:
    counts = model.counts
    lines = [
        "# Route B publication blueprint", "",
        "Generated by docs/cartographer/blueprint_gen.py; do not edit by hand.", "",
        "- Route status: CHALLENGER / NOT_RH",
        "- PX_RH_CLAIM: NOT_MADE",
        f"- Assembly rows: {counts['assembly_rows']}",
        f"- Publication-green exact receipts: {counts['green']}",
        f"- Validation-only rows: {counts['validation_only']}",
        f"- Open mathematical rows: {counts['open_math']}",
        f"- READY rows without exact declaration receipt: {counts['unresolved_receipt']}",
        "", "## Definitions and faithfulness interface", "",
        "Q3.RH is the classical open-strip RH proposition over Mathlib riemannZeta.",
        "Q3.RouteB.rh_iff_centeredXi_zeros_real is an equivalence, not a proof of RH.",
        "", "## Conditional roof", "",
        "Q3.RouteB.rh_of_canonical_strip_slots is kernel-checked and conditional.",
        "It does not close any open assembly row.",
    ]
    grouped: dict[str, list[Node]] = defaultdict(list)
    for node in model.nodes:
        grouped[node.row.chain].append(node)
    for chain in sorted(grouped):
        lines += ["", f"## {CHAIN_TITLES.get(chain, chain)}", ""]
        for node in grouped[chain]:
            row = node.row
            lines += [
                f"### Step {row.step}: {node.publication_status} — {row.requirement}", ""
            ]
            if node.receipt:
                lines += [
                    f"- Lean: {node.receipt.full_name}",
                    f"- Source module: {node.receipt.module}",
                    "- Axioms: " + (", ".join(node.receipt.axioms) or "none"),
                    "", "~~~lean", node.receipt.proof.statement or "", "~~~",
                ]
            else:
                lines.append(f"- Non-green reason: {node.reason}")
                if row.supplied_by:
                    lines.append(f"- Assembly supplier field: {row.supplied_by}")
                if row.note:
                    lines.append(f"- Recorded note: {row.note}")
            lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def render_manifest(model: Model) -> str:
    value = {
        "schema": SCHEMA,
        "git_head": model.git_head,
        "git_head_semantics": "latest commit touching tracked blueprint data inputs",
        "assembly_rows_digest": model.assembly_rows_digest,
        "proof_statement_digest": model.proof_statement_digest,
        "env_index_digest": model.env_index_digest,
        "generator_digest": model.generator_digest,
        "bibliography_path": "docs/routeB_bus/litreview/references.bib",
        "counts": model.counts,
        "route_status": "CHALLENGER",
        "rh_status": "NOT_RH",
        "PX_RH_CLAIM": "NOT_MADE",
    }
    return json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"


def outputs(model: Model) -> dict[Path, bytes]:
    files = {
        PREVIEW_PATH: render_preview(model),
        MANIFEST_PATH: render_manifest(model),
        SRC / "content.tex": render_content(model),
        SRC / "print.tex": r"""% Generated blueprint print driver.
\documentclass[11pt,a4paper]{article}
\usepackage[a4paper,margin=30mm]{geometry}
\usepackage{expl3}
\usepackage{amssymb,amsthm,mathtools}
\usepackage{fvextra}
\usepackage[unicode,colorlinks=true,linkcolor=blue,urlcolor=magenta,citecolor=blue]{hyperref}
\usepackage{fontspec}
\setmainfont{FreeSerif}
\setmonofont{FreeMono}
\input{macros/common}
\input{macros/print}
\title{Operator Methods for the Riemann Hypothesis: Route B Blueprint}
\author{}\date{}
\begin{document}\maketitle
\setlength{\emergencystretch}{3em}\sloppy
\input{content}\end{document}
""",
        SRC / "web.tex": r"""% Generated blueprint web driver.
\documentclass{article}
\usepackage{amssymb,amsthm,amsmath}
\usepackage{fvextra}
\usepackage{hyperref}
\usepackage[dep_graph]{blueprint}
\input{macros/common}
\input{macros/web}
\title{Operator Methods for the Riemann Hypothesis: Route B Blueprint}
\author{}
\begin{document}\maketitle\input{content}\end{document}
""",
        SRC / "blueprint.sty": "\\DeclareOption*{}\n\\ProcessOptions\n"
        "\\newcommand{\\graphcolor}[3]{}\n",
        SRC / "plastex.cfg": """[general]
renderer=HTML5
copy-theme-extras=yes
plugins=plastexdepgraph leanblueprint

[document]
toc-depth=2
toc-non-files=True

[files]
directory=../web/
split-level=2

[html5]
localtoc-level=1
extra-css=extra_styles.css
mathjax-dollars=False
""",
        SRC / "latexmkrc": "use Cwd qw(abs_path);\n"
        "my $q3_bib_dir = abs_path('../../../docs/routeB_bus/litreview');\n"
        "$ENV{'BIBINPUTS'} = $q3_bib_dir . ':' . ($ENV{'BIBINPUTS'} // '');\n"
        "$pdf_mode = 1;\n"
        "$pdflatex = 'xelatex -interaction=nonstopmode -halt-on-error -synctex=1 %O %S';\n"
        "@default_files = ('print.tex');\n",
        SRC / "macros/common.tex": r"""\theoremstyle{definition}
\newtheorem{theorem}{Theorem}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{validation}[theorem]{Validation record}
""",
        SRC / "macros/print.tex": r"""\newcommand{\lean}[1]{}
\newcommand{\discussion}[1]{}
\newcommand{\leanok}{}
\newcommand{\mathlibok}{}
\newcommand{\notready}{}
\ExplSyntaxOn
\NewDocumentCommand{\uses}{m}
 {\clist_map_inline:nn{#1}{\vphantom{\ref{##1}}}\ignorespaces}
\NewDocumentCommand{\proves}{m}
 {\clist_map_inline:nn{#1}{\vphantom{\ref{##1}}}\ignorespaces}
\ExplSyntaxOff
""",
        SRC / "macros/web.tex": "% Web-only macros.\n",
        SRC / "extra_styles.css": (
            "/* Validation records are evidence, not proof nodes. */\n"
            ".validation { border-left: .35rem solid #d97706; padding-left: .75rem; }\n"
        ),
    }
    return {path: text.encode() for path, text in files.items()}


def validate(model: Model, rendered: Mapping[Path, bytes]) -> None:
    counts = model.counts
    partition = (
        counts["green"] + counts["validation_only"] + counts["open_math"]
        + counts["unresolved_receipt"]
    )
    if partition != counts["assembly_rows"]:
        raise BlueprintError("publication categories do not partition assembly")
    for node in model.nodes:
        if (node.publication_status == "GREEN") != (node.receipt is not None):
            raise BlueprintError(f"receipt/status mismatch: {node.row.identity}")
    for path in (PREVIEW_PATH, SRC / "content.tex"):
        if b"PX_RH_CLAIM: NOT_MADE" not in rendered[path]:
            raise BlueprintError(f"honesty token missing from {path}")
    manifest = json.loads(rendered[MANIFEST_PATH])
    if manifest.get("PX_RH_CLAIM") != "NOT_MADE":
        raise BlueprintError("honesty token missing from manifest")


def publish(rendered: Mapping[Path, bytes]) -> None:
    staged = []
    for path, data in rendered.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(
            mode="wb", dir=path.parent, prefix=f".{path.name}.",
            suffix=".tmp", delete=False,
        ) as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
            staged.append((Path(handle.name), path))
    staged.sort(key=lambda pair: pair[1] == MANIFEST_PATH)
    for temporary, destination in staged:
        os.replace(temporary, destination)


def stale_paths(rendered: Mapping[Path, bytes]) -> list[Path]:
    return [
        path for path, expected in rendered.items()
        if not path.is_file() or path.read_bytes() != expected
    ]


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="read-only stale check")
    parser.add_argument(
        "--prepare-env",
        action="store_true",
        help="compile Route B and refresh EnvDump if its byte fingerprint changed",
    )
    args = parser.parse_args(argv)
    try:
        if args.check and args.prepare_env:
            raise BlueprintError("--check and --prepare-env are mutually exclusive")
        if args.prepare_env:
            prepare_env_index()
        model = build_model()
        rendered = outputs(model)
        validate(model, rendered)
        if args.check:
            stale = stale_paths(rendered)
            for path in stale:
                print(f"STALE: {path.relative_to(ROOT)}", file=sys.stderr)
            if stale:
                return 1
            print("blueprint check: OK")
            return 0
        publish(rendered)
        counts = model.counts
        print(
            f"blueprint generated: rows={counts['assembly_rows']} "
            f"green={counts['green']} validation={counts['validation_only']} "
            f"open={counts['open_math']} "
            f"unresolved_receipt={counts['unresolved_receipt']}"
        )
        return 0
    except (BlueprintError, OSError, sqlite3.Error, UnicodeError) as exc:
        print(f"blueprint generation failed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
