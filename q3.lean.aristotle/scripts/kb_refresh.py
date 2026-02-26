#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import datetime as dt
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
KB = ROOT / "KB"
INSIGHTS = KB / "insights"
OPEN_LEMMAS = KB / "maps" / "open_lemmas.md"
SESSION_STATE = KB / "SESSION_STATE.md"
AXIOM_REGISTRY = KB / "axioms" / "AXIOM_REGISTRY.md"

FRONTMATTER_RE = re.compile(r"^---\s*$")
SENTENCE_RE = re.compile(r"([^.!?]*[.!?])", re.M)
CHECK_AXIOMS_RE = re.compile(r"depends on axioms:\s*\[(.*?)\]", re.S)

ACCEPTED_AXIOMS = [
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Q3.Weil_criterion_tau0",
    "Lean.ofReduceBool",
    "Lean.trustCompiler",
]

AXIOM_FILE_HINTS = {
    "prime_b_grid_bounds_data": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean",
    "Q3.Proofs.PrimeCert.prime_b_grid_bounds_data": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean",
    "prime_b_grid_arch_bounds_data": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean",
    "Q3.Proofs.PrimeCert.prime_b_grid_arch_bounds_data": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeCert_2046.lean",
    "prime_b_grid_bucket_bounds": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean",
    "Q3.Proofs.PrimeCert.prime_b_grid_bucket_bounds": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean",
    "prime_heat_bounds_arch_data": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean",
    "Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean",
    "prime_heat_bucket_data": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean",
    "Q3.Proofs.PrimeCert.prime_heat_bucket_data": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean",
    "prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowAutoGT10000Fallback.lean",
    "Q3.Proofs.PrimeCert.prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all": "q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowAutoGT10000Fallback.lean",
    "prime_heat_margin_cert_2026_01_28": "q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeHeatMarginWitness_2026_01_28.lean",
    "Q3.Proofs.PrimeCert.prime_heat_margin_cert_2026_01_28": "q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeHeatMarginWitness_2026_01_28.lean",
}

AXIOM_CLOSURE_PATH = {
    "prime_b_grid_bounds_data": "Formalize grid certificate or analytic bound",
    "Q3.Proofs.PrimeCert.prime_b_grid_bounds_data": "Formalize grid certificate or analytic bound",
    "prime_b_grid_arch_bounds_data": "Formalize arch-term lower bound at grid nodes",
    "Q3.Proofs.PrimeCert.prime_b_grid_arch_bounds_data": "Formalize arch-term lower bound at grid nodes",
    "prime_b_grid_bucket_bounds": "Formalize bucketed prime-term upper bounds on grid",
    "Q3.Proofs.PrimeCert.prime_b_grid_bucket_bounds": "Formalize bucketed prime-term upper bounds on grid",
    "prime_heat_bounds_arch_data": "Formalize arch integral bound",
    "Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data": "Formalize arch integral bound",
    "prime_heat_bucket_data": "Formalize bucket partial sums",
    "Q3.Proofs.PrimeCert.prime_heat_bucket_data": "Formalize bucket partial sums",
    "prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all": "Discharge GT10000 auto shards and remove fallback axiom",
    "Q3.Proofs.PrimeCert.prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all": "Discharge GT10000 auto shards and remove fallback axiom",
    "prime_heat_margin_cert_2026_01_28": "Replace witness with fully formal PrimeHeat margin checker soundness",
    "Q3.Proofs.PrimeCert.prime_heat_margin_cert_2026_01_28": "Replace witness with fully formal PrimeHeat margin checker soundness",
}


def unique_preserve_order(items: list[str]) -> list[str]:
    seen = set()
    out: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def short_axiom_name(name: str) -> str:
    return name.split(".")[-1]


def axiom_file_hint(name: str) -> str:
    return AXIOM_FILE_HINTS.get(name, "(file mapping TODO)")


def axiom_closure_hint(name: str) -> str:
    return AXIOM_CLOSURE_PATH.get(name, "Formalize theorem and remove axiom")


def latest_insight_path() -> str:
    if not INSIGHTS.exists():
        return "(none)"
    candidates = [p for p in INSIGHTS.glob("*.md") if p.name != "INDEX.md"]
    if not candidates:
        return "(none)"
    latest = max(candidates, key=lambda p: p.stat().st_mtime)
    return f"KB/insights/{latest.name}"


def parse_mainline_axioms(text: str) -> list[str]:
    m = CHECK_AXIOMS_RE.search(text)
    if not m:
        return []
    body = m.group(1).replace("\n", " ")
    chunks = [c.strip().strip("'") for c in body.split(",")]
    axioms = [c for c in chunks if c]
    return unique_preserve_order(axioms)


def run_check_axioms() -> list[str]:
    cmd = ["lake", "env", "lean", "Q3/CheckAxioms.lean"]
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, check=False)
    text = (proc.stdout or "") + "\n" + (proc.stderr or "")
    if proc.returncode != 0:
        print("kb_refresh: failed to run Q3/CheckAxioms.lean", flush=True)
        return []
    axioms = parse_mainline_axioms(text)
    if not axioms:
        print("kb_refresh: unable to parse mainline axioms from CheckAxioms output", flush=True)
        return []
    return axioms


def strip_frontmatter(text: str) -> str:
    lines = text.splitlines()
    if lines and FRONTMATTER_RE.match(lines[0]):
        # find closing ---
        for i in range(1, len(lines)):
            if FRONTMATTER_RE.match(lines[i]):
                return "\n".join(lines[i + 1 :])
    return text


def summarize(text: str) -> str:
    body = strip_frontmatter(text)
    # drop headings
    lines = [ln.strip() for ln in body.splitlines() if ln.strip()]
    lines = [ln for ln in lines if not ln.startswith("#")]
    if not lines:
        return "(no summary)"
    joined = " ".join(lines)
    # take first 1-2 sentences
    sentences = SENTENCE_RE.findall(joined)
    if sentences:
        summary = " ".join(sentences[:2]).strip()
    else:
        summary = joined[:200].strip()
    return summary[:240] + ("…" if len(summary) > 240 else "")


def refresh_insights_index() -> None:
    if not INSIGHTS.exists():
        return
    stamp = dt.date.today().isoformat()
    items = []
    for p in sorted(INSIGHTS.glob("*.md")):
        if p.name == "INDEX.md":
            continue
        try:
            summary = summarize(p.read_text(encoding="utf-8"))
        except Exception:
            summary = "(unreadable)"
        items.append((p.name, summary))
    out = [
        "---",
        "tags: [pipeline]",
        "priority: low",
        f"last_updated: {stamp}",
        "---",
        "",
        "# Insights index",
        "",
        "Auto-generated by scripts/kb_refresh.py.",
        "",
        "Files:",
        "",
    ]
    for name, summary in items:
        out.append(f"- {name} — {summary}")
    (INSIGHTS / "INDEX.md").write_text("\n".join(out) + "\n", encoding="utf-8")


def refresh_open_lemmas_scan() -> None:
    if not OPEN_LEMMAS.exists():
        return
    target_root = ROOT / "Q3"
    if not target_root.exists():
        return

    axiom_decl = re.compile(r"^\s*axiom\b")
    axiom_name = re.compile(r"^\s*axiom\s+([A-Za-z0-9_'.]+)")
    hole_patterns = [
        re.compile(r"\bsorry\b"),
        re.compile(r"\badmit\b"),
        re.compile(r"exact\?"),
    ]

    per_file: dict[str, dict[str, list[tuple[int, str]]]] = {}

    for p in sorted(target_root.rglob("*.lean")):
        rel = p.relative_to(ROOT)
        # skip archive/clean to keep list focused
        if "Archive" in rel.parts or "Clean" in rel.parts:
            continue
        if rel == Path("Q3/Axioms.lean"):
            # Q3/Axioms.lean is intentionally axiom-heavy; we track mainline blockers separately.
            continue
        try:
            lines = p.read_text(encoding="utf-8").splitlines()
        except Exception:
            continue
        axioms: list[tuple[int, str]] = []
        holes: list[tuple[int, str]] = []
        for i, line in enumerate(lines, 1):
            stripped = line.lstrip()
            if stripped.startswith("--"):
                continue
            if axiom_decl.search(line):
                snippet = line.strip()
                if len(snippet) > 140:
                    snippet = snippet[:137] + "…"
                axioms.append((i, snippet))
                continue
            if any(rx.search(line) for rx in hole_patterns):
                snippet = line.strip()
                if len(snippet) > 140:
                    snippet = snippet[:137] + "…"
                holes.append((i, snippet))
        if axioms or holes:
            per_file[str(rel)] = {"axioms": axioms, "holes": holes}

    stamp = dt.date.today().isoformat()
    block = [
        "## Auto scan (raw)",
        f"Generated: {stamp}",
        "",
        "Format: `<file>` — `axioms=<n>` `holes=<m>` (names/line hints).",
        "",
    ]
    for rel in sorted(per_file.keys()):
        axioms = per_file[rel]["axioms"]
        holes = per_file[rel]["holes"]

        ax_names: list[str] = []
        for _ln, snip in axioms:
            m = axiom_name.match(snip)
            if m:
                ax_names.append(m.group(1))
        ax_names = sorted(set(ax_names))
        ax_hint = ""
        if ax_names:
            shown = ", ".join(ax_names[:3]) + ("…" if len(ax_names) > 3 else "")
            ax_hint = f" (axioms: {shown})"

        hole_lines = [ln for ln, _snip in holes]
        hole_hint = ""
        if hole_lines:
            shown = ", ".join(str(n) for n in hole_lines[:5]) + ("…" if len(hole_lines) > 5 else "")
            hole_hint = f" (holes at: {shown})"

        block.append(f"- {rel} — axioms={len(axioms)} holes={len(holes)}{ax_hint}{hole_hint}")

    content = OPEN_LEMMAS.read_text(encoding="utf-8")
    start = content.find("<!-- AUTO:SCAN_START -->")
    end = content.find("<!-- AUTO:SCAN_END -->")
    if start == -1 or end == -1 or end <= start:
        return

    new_block = "<!-- AUTO:SCAN_START -->\n" + "\n".join(block) + "\n<!-- AUTO:SCAN_END -->"
    updated = content[:start] + new_block + content[end + len("<!-- AUTO:SCAN_END -->") :]
    OPEN_LEMMAS.write_text(updated, encoding="utf-8")


def refresh_session_state(mainline_axioms: list[str]) -> None:
    if not SESSION_STATE.exists():
        return
    stamp = dt.date.today().isoformat()
    pending = [ax for ax in mainline_axioms if ax not in ACCEPTED_AXIOMS]

    lines = [
        "---",
        "tags: [proof, axiom, pipeline]",
        "priority: high",
        f"last_updated: {stamp}",
        "---",
        "",
        "# SESSION_STATE",
        "",
        "Current chain: Single-scale, t_critical = 3/20, tau = 0, BaseAtomCone (B-range).",
        "",
        "Accepted axioms (do NOT close):",
        "- Standard: `propext`, `Classical.choice`, `Quot.sound`",
        "- Weil: `Q3.Weil_criterion_tau0`",
        "",
        "Mainline axioms to close (remaining work):",
    ]
    if pending:
        for ax in pending:
            lines.append(f"- `{ax}` in `{axiom_file_hint(ax)}`")
    else:
        lines.append("- none")

    lines.extend(
        [
            "",
            "Next expected step:",
            "- Follow `KB/axioms/closure_plan.md` (priority order + success checks).",
            "",
            "Checklist (close remaining mainline axioms):",
        ]
    )

    if pending:
        for ax in pending:
            lines.append(
                f"- [ ] Replace `{short_axiom_name(ax)}` with theorem in `{axiom_file_hint(ax)}`."
            )
    else:
        lines.append("- [ ] No pending mainline axioms to close.")

    lines.extend(
        [
            "- [ ] Verify: `lake env lean Q3/CheckAxioms.lean` shows only standard + Weil.",
            "- [ ] Verify: `./scripts/check_axioms.sh` clean.",
            "- [ ] Update: `KB/axioms/AXIOM_REGISTRY.md`, `KB/maps/open_lemmas.md`, and add 1 new `KB/insights/YYYY-MM-DD_*.md`.",
            "",
            "Last synthesis:",
            f"- `{latest_insight_path()}`",
            "",
            "Open lemmas list:",
            "- `KB/maps/open_lemmas.md`",
            "",
        ]
    )
    SESSION_STATE.write_text("\n".join(lines), encoding="utf-8")


def refresh_axiom_registry(mainline_axioms: list[str]) -> None:
    if not AXIOM_REGISTRY.exists():
        return
    stamp = dt.date.today().isoformat()
    pending = [ax for ax in mainline_axioms if ax not in ACCEPTED_AXIOMS]

    lines = [
        "---",
        "tags: [axiom, proof]",
        "priority: high",
        f"last_updated: {stamp}",
        "---",
        "",
        "# Axiom Registry (Mainline)",
        "",
        "This is the authoritative list of axioms relevant to the current tau=0 main chain.",
        "LaTeX is primary for meaning; Lean is primary for status.",
        "",
        "## Core accepted (do NOT close)",
        "| Axiom | Category | Lean file | Status | Notes |",
        "| --- | --- | --- | --- | --- |",
        "| `propext` | standard | Lean core | accepted | Foundational |",
        "| `Classical.choice` | standard | Lean core | accepted | Foundational |",
        "| `Quot.sound` | standard | Lean core | accepted | Foundational |",
        "| `Q3.Weil_criterion_tau0` | Weil | `q3.lean.aristotle/Q3/Axioms.lean` | accepted | Community-standard (Weil 1952) |",
        "",
        "## Mainline (must close)",
        "| Axiom | Category | Lean file | Status | Closure path |",
        "| --- | --- | --- | --- | --- |",
    ]

    if pending:
        for ax in pending:
            lines.append(
                f"| `{ax}` | cert | `{axiom_file_hint(ax)}` | open | {axiom_closure_hint(ax)} |"
            )
    else:
        lines.append("| none | n/a | n/a | closed | No pending mainline axioms |")

    lines.extend(
        [
            "",
            "## Off-chain / legacy (not in tau=0 main chain)",
            "| Axiom | Lean file | Notes |",
            "| --- | --- | --- |",
            "| `prime_term_le_at_t_critical_axiom` | `q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean` | off-chain (tau != 0) |",
            "| `Q_nonneg_on_BaseAtomCone_axiom` | `q3.lean.aristotle/Q3/Proofs/Q_nonneg_base_atoms.lean` | legacy bridge |",
            "",
            "## Update rule",
            "Refresh after `Q3/CheckAxioms.lean` or any PrimeCert certificate update.",
            "",
        ]
    )
    AXIOM_REGISTRY.write_text("\n".join(lines), encoding="utf-8")


def refresh_mainline_axiom_state() -> None:
    axioms = run_check_axioms()
    if not axioms:
        return
    refresh_session_state(axioms)
    refresh_axiom_registry(axioms)


def main() -> None:
    refresh_insights_index()
    refresh_open_lemmas_scan()
    refresh_mainline_axiom_state()


if __name__ == "__main__":
    main()
