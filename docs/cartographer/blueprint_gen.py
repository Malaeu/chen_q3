#!/usr/bin/env python3
"""blueprint_gen — скелет статьи ИЗ БАЗЫ (PUBLICATION_PLAN, механика).

Статья = второй дашборд assembly: опора -> секция, канат -> лемма со
statement из aristotle_proofs.db и ссылкой \\lean{...}. Закреплённое --
зелёным, висящее -- красным с измеренным типом дыры. Ничего не пишется
вперёд математики: закрыл канат -> узел позеленел.

Выход: full/blueprint/blueprint.md (превью) — LaTeX-рендер тем же скриптом
позже, когда решим формат (leanblueprint vs свой каркас по RH_Q3.tex).
"""
import sqlite3, pathlib, datetime

ROOT = pathlib.Path(__file__).resolve().parents[2]
KB   = f"file:{ROOT}/q3.lean.aristotle/aristotle_db/knowledge.db?mode=ro"
PDB  = f"file:{ROOT}/q3.lean.aristotle/aristotle_db/aristotle_proofs.db?mode=ro"
OUT  = ROOT / "full" / "blueprint" / "blueprint.md"

GATE = {  # дорога -> опора (сверено 2026-08-19/20)
    "PSD_CERTIFICATE_FOR_CCM_CELL": ("G2", "Pillar G2 — simple even ground (validation cell)"),
    "SIMPLE_EVEN_GROUND_TO_REAL_ZEROS": ("G3", "Pillar G3 — real zeros bridge (Theorem 5.10)"),
    "GOAL057_CONTINUUM_NUMERATOR_BRIDGE": ("G6", "Pillar G6 — S2 wall: continuum numerator"),
    "REALZERO_GROUND_DIAGONAL_TO_XI": ("058", "Route 058 — ground diagonal to Xi (replaces G2+G3)"),
}

def statement_of(name, pconn):
    if not name: return None
    row = pconn.execute(
        "select statement from lemmas where name=? limit 1", (name.strip(),)).fetchone()
    return row[0] if row else None

def main():
    kb = sqlite3.connect(KB, uri=True); pdb = sqlite3.connect(PDB, uri=True)
    lines = [
        "# Blueprint — Operator Methods for RH (skeleton, generated from assembly)",
        "",
        f"*Generated {datetime.date.today().isoformat()} by blueprint_gen.py — DO NOT edit by hand:*",
        "*regenerate after any assembly change. Green = kernel-proved rope,*",
        "*red = hanging rope with its measured hole. Roof and Hurwitz transfer are concrete.*",
        "",
        "## §0 Main Theorem and definitional faithfulness  ✅ (proved interface)",
        "",
        "- `Q3.RH` := ∀ s, riemannZeta s = 0 → 0 < re s < 1 → re s = 1/2  (`Q3/Basic/Defs.lean:177`, Mathlib zeta)",
        "- Bridge: `rh_iff_centeredXi_zeros_real` (`ClassicalXiInterface.lean:108`) ✅",
        "",
        "## §1 Roof  ✅",
        "",
        "- `rh_of_canonical_strip_slots` (`CanonicalRHRouteSkeleton.lean:145`) — conditional, hole-free ✅",
        "- Hurwitz transfer: `ZeroEscapeLogic` + `MontelNormalFamilies` ✅",
        "",
    ]
    for chain, (gid, title) in GATE.items():
        rows = kb.execute(
            "select step, requirement, supplied_by, supplier_file, status, note "
            "from assembly where chain=? order by step", (chain,)).fetchall()
        done = sum(1 for r in rows if r[4] in ("READY", "VALIDATION"))
        lines += [f"## §{gid} {title}  — {done}/{len(rows)} ropes fastened", ""]
        for step, req, sup, sfile, status, note in rows:
            if status in ("READY", "VALIDATION"):
                mark = "✅" if status == "READY" else "☑ (validation-only, off critical path)"
                lean = f" — `\\lean{{{sup}}}` `{sfile}`" if sup else ""
                lines.append(f"- {mark} **{step}.** {req}{lean}")
                st = statement_of(sup, pdb)
                if st:
                    lines.append(f"  - `{st[:220]}`")
            else:
                lines.append(f"- 🔴 **{step}.** {req}  *[{status}]*")
                if note:
                    lines.append(f"  - hole: {note[:200]}")
        lines.append("")
    lines += [
        "## §A Attribution (from provenance counter)",
        "",
        "- our Lean / Mathlib / data per pillar — see session_start ОПОРЫ И КАНАТЫ;",
        "- paper engines (Connes, CvS): blueprints, not premises — port status per verdicts.",
        "",
    ]
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(lines), encoding="utf-8")
    total = sum(1 for _ in lines)
    print(f"blueprint: {OUT.relative_to(ROOT)} ({total} строк)")

if __name__ == "__main__":
    main()
