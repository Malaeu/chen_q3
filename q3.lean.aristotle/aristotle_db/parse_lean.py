#!/usr/bin/env python3
"""
Lean 4 Parser for Aristotle Proofs Database
Parses .lean files and extracts lemmas/theorems/definitions
"""

import sqlite3
import re
import json
import os
from pathlib import Path
from typing import Optional

DB_PATH = Path(__file__).parent / "aristotle_proofs.db"

# Regex patterns for Lean 4
LEMMA_PATTERN = re.compile(
    r'^(lemma|theorem|def)\s+(\w+)\s*(.*?)(?::=|:|\bwhere\b)',
    re.MULTILINE | re.DOTALL
)

# Markers for incomplete proofs in Aristotle outputs.
INCOMPLETE_PATTERN = re.compile(r'\b(sorry|admit)\b')

# Pattern to find the full declaration including type
# Handles: lemma foo {x : T} (y : T) : RetType := by
#          def bar (x : T) : T := ...
#          theorem baz : Statement := by
#          noncomputable def qux : T := ...
#          private lemma helper : T := by
DECL_PATTERN = re.compile(
    r'^(?:(?:noncomputable|private|protected)\s+)*(lemma|theorem|def|abbrev)\s+(\w+)\s*([\{\[\(].*?)?(?::\s*(.+?))?\s*:=',
    re.MULTILINE | re.DOTALL
)

# Known Mathlib lemmas (partial list for dependency detection)
MATHLIB_LEMMAS = {
    'tsum_congr', 'Summable.tsum_pos', 'Summable.of_nonneg_of_le',
    'Complex.im_tsum', 'HasDerivAt.deriv', 'AnalyticAt.differentiableAt',
    'Filter.Tendsto', 'Real.summable_one_div_nat_pow', 'Finset.sum_range_succ',
    'Complex.continuous_re', 'Complex.continuous_im'
}

DOC_STATUS_OVERRIDES = {
    "A3_FLOOR_v9": "in_progress",
    "A3_FLOOR_v11_fixed": "in_progress",
}

LEMMA_STATUS_OVERRIDES = {
    ("A3_FLOOR_v9", "deriv_a_pos"): "in_progress",
    ("A3_FLOOR_v9", "strictMonoOn_a"): "in_progress",
    ("A3_FLOOR_v11_fixed", "deriv_a_neg"): "in_progress",
    ("A3_FLOOR_v11_fixed", "strictAntiOn_a"): "in_progress",
}

LEMMA_NOTES_OVERRIDES = {
    ("A3_FLOOR_v9", "deriv_a_pos"): (
        "Conditional: uses opaque digamma/trigamma/a; depends on "
        "deriv_digamma_eq_trigamma; deriv_a_eq sign mismatch vs v3."
    ),
    ("A3_FLOOR_v9", "strictMonoOn_a"): (
        "Conditional: uses opaque digamma/trigamma/a; depends on "
        "deriv_digamma_eq_trigamma; deriv_a_eq sign mismatch vs v3."
    ),
    ("A3_FLOOR_v11_fixed", "deriv_a_neg"): (
        "Conditional: uses axiom deriv_digamma_eq_trigamma; correct sign."
    ),
    ("A3_FLOOR_v11_fixed", "strictAntiOn_a"): (
        "Conditional: uses axiom deriv_digamma_eq_trigamma; correct sign."
    ),
    ("A3_FLOOR_v16", "tendstoUniformlyOn_div_of_bounds"): (
        "Bridge lemma proved; requires lower bound on g and boundedness of f on K."
    ),
    ("A3_FLOOR_v16", "digammaSeq_tendstoLocallyUniformlyOn_of_derivGamma_bounded"): (
        "Uses boundedness of deriv Gamma on compact subsets."
    ),
    ("A3_FLOOR_v16", "deriv_digamma_eq_trigamma_of_derivGamma_bounded"): (
        "Uses boundedness of deriv Gamma on compact subsets."
    ),
    ("A3_FLOOR_v16", "deriv_digamma_eq_trigamma"): (
        "Uses boundedness of deriv Gamma on compact subsets."
    ),
}

def get_connection():
    """Get database connection."""
    return sqlite3.connect(DB_PATH)


def parse_lean_file(file_path: Path) -> list[dict]:
    """Parse a .lean file and extract declarations."""
    content = file_path.read_text(encoding='utf-8')
    lines = content.split('\n')

    declarations = []

    # Find all declarations
    for match in DECL_PATTERN.finditer(content):
        kind = match.group(1)  # lemma/theorem/def/abbrev
        name = match.group(2)  # name
        params = match.group(3) or ''  # parameters {x : T} (y : T)
        ret_type = match.group(4) or ''  # return type

        # Get line number
        line_start = content[:match.start()].count('\n') + 1

        # Find end of proof (next lemma/theorem/def or end of file)
        end_pos = match.end()
        next_match = DECL_PATTERN.search(content, end_pos)
        if next_match:
            proof_end = next_match.start()
        else:
            proof_end = len(content)

        line_end = content[:proof_end].count('\n') + 1

        # Extract statement
        statement = f"{kind} {name} {params.strip()}"
        if ret_type:
            statement += f" : {ret_type.strip()[:200]}"  # Truncate long types

        # Detect dependencies from proof body
        proof_body = content[match.end():proof_end]
        deps = detect_dependencies(proof_body)

        # Check if proof has incomplete markers
        has_sorry = INCOMPLETE_PATTERN.search(proof_body) is not None

        declarations.append({
            'kind': kind,
            'name': name,
            'statement': statement[:500],  # Truncate long statements
            'line_start': line_start,
            'line_end': line_end,
            'deps': deps,
            'has_sorry': has_sorry
        })

    return declarations


def detect_dependencies(proof_body: str) -> list[str]:
    """Detect lemma dependencies in proof body."""
    deps = []

    # Check for known Mathlib lemmas
    for lemma in MATHLIB_LEMMAS:
        if lemma in proof_body:
            deps.append(lemma)

    # Check for local lemma references (heuristic: words ending in _neg, _pos, etc.)
    local_refs = re.findall(r'\b(\w+_(?:neg|pos|eq|bound|summable|add_one|tendsto))\b', proof_body)
    deps.extend(set(local_refs))

    return list(set(deps))


def insert_doc(conn, doc_id: str, path: str, approach: str, priority: str,
               status: str, stage: str = None, source: str = 'aristotle',
               aristotle_uuid: str = None, lines: int = 0, size_bytes: int = 0):
    """Insert a document record."""
    cursor = conn.cursor()
    cursor.execute('''
        INSERT OR REPLACE INTO docs
        (doc_id, path, approach, priority, status, stage, source, aristotle_uuid, lines, size_bytes)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    ''', (doc_id, path, approach, priority, status, stage, source, aristotle_uuid, lines, size_bytes))
    conn.commit()


def insert_lemma(conn, lemma_id: str, name: str, doc_id: str, status: str,
                 priority: str, statement: str, deps_json: str, notes: str = None,
                 line_start: int = 0, line_end: int = 0):
    """Insert a lemma record."""
    cursor = conn.cursor()
    cursor.execute('''
        INSERT OR REPLACE INTO lemmas
        (lemma_id, name, doc_id, status, priority, statement, deps_json, notes, line_start, line_end)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    ''', (lemma_id, name, doc_id, status, priority, statement, deps_json, notes, line_start, line_end))
    conn.commit()


def insert_spec(conn, spec_id: str, section: str, key: str, value: str,
                approach: str, source_path: str):
    """Insert a spec record."""
    cursor = conn.cursor()
    cursor.execute('''
        INSERT OR REPLACE INTO specs
        (spec_id, section, key, value, approach, source_path)
        VALUES (?, ?, ?, ?, ?, ?)
    ''', (spec_id, section, key, value, approach, source_path))
    conn.commit()


def import_lean_file(file_path: Path, doc_id: str, approach: str, priority: str,
                     stage: str = None, aristotle_uuid: str = None):
    """Import a .lean file into the database."""
    conn = get_connection()

    # Get file stats
    stat = file_path.stat()
    content = file_path.read_text(encoding='utf-8')
    lines = len(content.split('\n'))

    # Parse and insert lemmas
    declarations = parse_lean_file(file_path)
    doc_status = DOC_STATUS_OVERRIDES.get(doc_id)
    if doc_status is None:
        doc_status = "in_progress" if any(decl["has_sorry"] for decl in declarations) else "proven"
    insert_doc(
        conn, doc_id, str(file_path), approach, priority, doc_status,
        stage, 'aristotle', aristotle_uuid, lines, stat.st_size
    )
    for decl in declarations:
        lemma_id = f"{decl['name']}_{doc_id}"
        status = LEMMA_STATUS_OVERRIDES.get(
            (doc_id, decl["name"]),
            "sorry" if decl["has_sorry"] else "proven",
        )
        notes = LEMMA_NOTES_OVERRIDES.get((doc_id, decl["name"]))
        insert_lemma(
            conn, lemma_id, decl['name'], doc_id, status, priority,
            decl['statement'], json.dumps(decl['deps']), notes,
            decl['line_start'], decl['line_end']
        )

    conn.close()
    return len(declarations)


def import_specs_from_project_specs(file_path: Path):
    """Import specs from docs/PROJECT_SPECS.md."""
    conn = get_connection()

    # First insert as doc
    content = file_path.read_text(encoding='utf-8')
    lines = len(content.split('\n'))
    stat = file_path.stat()

    insert_doc(
        conn, 'PROJECT_SPECS', str(file_path), 'NEW_KERNEL', 'HIGH',
        'proven', None, 'spec', None, lines, stat.st_size
    )

    # Specs from §7 Ключевые инварианты
    specs = [
        ('sign', '§1', 'sign', 'Q = Q_arch - Q_prime'),
        ('normalization', '§1', 'normalization', 'ξ_n = log(n)/(2π), a_* = 2π*a'),
        ('torus', '§1', 'torus', 'period-1, T = [-1/2, 1/2]'),
        ('symbol', '§1', 'symbol', 'P_A = 2π Σ g(θ+m)'),
        ('c_star', '§3', 'c_star', '11/10'),
        ('c_star_constraint', '§7', 'floor', 'c_* = 11/10 (NOT 1.5!)'),
        ('toeplitz_gap', '§4', 'toeplitz_gap', 'ω(1/(2M)), M_0 = ⌈C_SB * L_* / c_*⌉'),
        ('prime_cap', '§3', 'prime_cap', 't_rkhs ≥ 1 ⟹ ρ(1) < 1/25'),
        ('goal', '§5', 'goal', 'Q(Φ) ≥ 0 (NOT ≥1.125!)'),
    ]

    for spec_id, section, key, value in specs:
        insert_spec(conn, spec_id, section, key, value, 'NEW_KERNEL', str(file_path))

    conn.close()
    return len(specs)


def list_docs():
    """List all documents in database."""
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT doc_id, approach, priority, status, lines FROM docs ORDER BY priority, doc_id')
    rows = cursor.fetchall()
    conn.close()
    return rows


def list_lemmas(doc_id: str = None):
    """List lemmas, optionally filtered by doc_id."""
    conn = get_connection()
    cursor = conn.cursor()
    if doc_id:
        cursor.execute('SELECT lemma_id, name, status, line_start FROM lemmas WHERE doc_id = ?', (doc_id,))
    else:
        cursor.execute('SELECT lemma_id, name, doc_id, status FROM lemmas ORDER BY name')
    rows = cursor.fetchall()
    conn.close()
    return rows


def list_specs():
    """List all specs."""
    conn = get_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT spec_id, section, key, value FROM specs ORDER BY section')
    rows = cursor.fetchall()
    conn.close()
    return rows


if __name__ == '__main__':
    import sys

    if len(sys.argv) < 2:
        print("Usage: parse_lean.py <command> [args]")
        print("Commands:")
        print("  import <file.lean> <doc_id> <approach> <priority> [stage] [uuid]")
        print("  import-specs <docs/PROJECT_SPECS.md>")
        print("  list-docs")
        print("  list-lemmas [doc_id]")
        print("  list-specs")
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == 'import' and len(sys.argv) >= 6:
        file_path = Path(sys.argv[2])
        doc_id = sys.argv[3]
        approach = sys.argv[4]
        priority = sys.argv[5]
        stage = sys.argv[6] if len(sys.argv) > 6 else None
        uuid = sys.argv[7] if len(sys.argv) > 7 else None

        count = import_lean_file(file_path, doc_id, approach, priority, stage, uuid)
        print(f"Imported {count} declarations from {file_path}")

    elif cmd == 'import-specs' and len(sys.argv) >= 3:
        file_path = Path(sys.argv[2])
        count = import_specs_from_project_specs(file_path)
        print(f"Imported {count} specs from {file_path}")

    elif cmd == 'list-docs':
        for row in list_docs():
            print(f"{row[0]:40} {row[1]:12} {row[2]:10} {row[3]:12} {row[4]} lines")

    elif cmd == 'list-lemmas':
        doc_id = sys.argv[2] if len(sys.argv) > 2 else None
        for row in list_lemmas(doc_id):
            print(f"{row[0]:50} {row[1]:30} {row[2] if len(row) > 2 else ''}")

    elif cmd == 'list-specs':
        for row in list_specs():
            print(f"{row[0]:20} {row[1]:5} {row[2]:20} {row[3]}")

    else:
        print(f"Unknown command: {cmd}")
        sys.exit(1)
