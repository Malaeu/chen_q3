#!/usr/bin/env python3
"""Refresh the repository-native flat Proshka mirror in docs/routeB_bus.

The destination boundary is deliberately hard-coded and checked.  No path
outside docs/routeB_bus in the canonical repository is created, removed, or
modified.
"""

from __future__ import annotations

import hashlib
import shutil
import subprocess
from pathlib import Path


REQUEST_DIR = Path(__file__).resolve().parent
Q3_ROOT = REQUEST_DIR.parents[2]
LEAN_DIR = Q3_ROOT / "Q3" / "Proofs" / "RouteB"
REPOSITORY_ROOT = Q3_ROOT.parent.resolve()
DESTINATION = (REPOSITORY_ROOT / "docs" / "routeB_bus").resolve()
RESYNC_REQUIRED_SOURCES = (
    REQUEST_DIR / "PROOF_COMPILER_RESYNC_2026-07-27.md",
    REQUEST_DIR / "PROOF_COMPILER_SEVEN_GATES_2026-07-27.json",
    REQUEST_DIR / "proshka" / "PROSHKA_RESYNC_AUDIT_2026-07-27.md",
    REQUEST_DIR / "proshka" / "PROSHKA_PEN_REDUCTIONS_2026-07-27.md",
    REQUEST_DIR / "027_hlambda_outer_lobe_gate.answer.md",
)
GOAL_028_REQUIRED_SOURCES = (
    REQUEST_DIR / "028R_finite_core_theta_order_audit.answer.md",
    REQUEST_DIR / "FINITE_CORE_THETA_CERT.json",
    REQUEST_DIR / "finite_core_theta_certificate.py",
    REQUEST_DIR / "check_finite_core_theta_certificate.py",
    REQUEST_DIR / "029_decisive_k_escalation.answer.md",
    REQUEST_DIR / "DECISIVE_FINITE_CORE_THETA_K_ESCALATION.json",
    REQUEST_DIR / "decisive_finite_core_theta_k_escalation.py",
    REQUEST_DIR / "check_decisive_finite_core_theta_k_escalation.py",
)
GOAL_030_REQUIRED_SOURCES = (
    REQUEST_DIR / "030_coupled_full_sum_response.answer.md",
    REQUEST_DIR / "COUPLED_FULL_SUM_RESPONSE_CERT.json",
    REQUEST_DIR / "coupled_full_sum_response_certificate.py",
    REQUEST_DIR / "check_coupled_full_sum_response_certificate.py",
)
GOAL_031_REQUIRED_SOURCES = (
    REQUEST_DIR / "031_priority_band_positive_part.answer.md",
    REQUEST_DIR / "PRIORITY_BAND_POSITIVE_PART_CERT.json",
    REQUEST_DIR / "priority_band_positive_part_certificate.py",
    REQUEST_DIR / "check_priority_band_positive_part_certificate.py",
)
GOAL_032_REQUIRED_SOURCES = (
    REQUEST_DIR / "ARISTOTLE_TASK_RiemannBoundaryCellBridge.md",
    REQUEST_DIR / "aristotle_bridge" / "RESULT.md",
    REQUEST_DIR / "aristotle_bridge" / "lakefile.toml",
    REQUEST_DIR / "aristotle_bridge" / "lean-toolchain",
    REQUEST_DIR / "aristotle_bridge" / "RequestProject" / "Main.lean",
    REQUEST_DIR
    / "aristotle_bridge"
    / "RequestProject"
    / "RiemannBoundaryCellBridge.lean",
)

def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def role(path: Path) -> str:
    name = path.name
    if name.endswith(".goal.md"):
        return "goal"
    if name.endswith(".answer.md"):
        return "answer"
    if path.parent.name == "proshka":
        return "Proshka verdict/source review"
    if name.startswith("ARISTOTLE_TASK_"):
        return "active Aristotle contract"
    if name.endswith(".lean"):
        return "key Lean artifact"
    if name.endswith(".csv"):
        return "probe data"
    if "_REPORT_" in name:
        return "measurement report"
    if "_PROBE" in name:
        return "probe report"
    return "Route B artifact"


def selected_sources() -> list[Path]:
    paths: set[Path] = set()
    for pattern in (
        "[0-9][0-9][0-9]_*.goal.md",
        "[0-9][0-9][0-9]_*.answer.md",
        "*_PROBE.md",
        "*_PROBE.csv",
        "*_REPORT_*.md",
    ):
        paths.update(path for path in REQUEST_DIR.glob(pattern) if path.is_file())
    paths.update(
        path
        for path in (REQUEST_DIR / "proshka").glob("*.md")
        if path.is_file()
    )
    paths.update(
        path
        for path in REQUEST_DIR.glob("ARISTOTLE_TASK_*v2_REPAIRED*.md")
        if path.is_file()
    )
    for path in (
        RESYNC_REQUIRED_SOURCES
        + GOAL_028_REQUIRED_SOURCES
        + GOAL_030_REQUIRED_SOURCES
        + GOAL_031_REQUIRED_SOURCES
        + GOAL_032_REQUIRED_SOURCES
    ):
        if not path.is_file():
            raise FileNotFoundError(
                f"PROSHKA_CHANNEL_RESYNC_SOURCE_MISSING:{path}"
            )
        paths.add(path)
    route_b_lean = sorted(LEAN_DIR.glob("*.lean"))
    if not route_b_lean:
        raise FileNotFoundError(
            f"PROSHKA_CHANNEL_ROUTE_B_LEAN_EMPTY:{LEAN_DIR}"
        )
    paths.update(path for path in route_b_lean if path.is_file())
    return sorted(paths, key=lambda path: path.name)


def git_output(*args: str) -> str:
    return subprocess.check_output(
        ("git", *args),
        cwd=Q3_ROOT.parent,
        text=True,
    ).strip()


def main() -> None:
    expected = (REPOSITORY_ROOT / "docs" / "routeB_bus").resolve()
    if DESTINATION != expected or REPOSITORY_ROOT not in DESTINATION.parents:
        raise RuntimeError(f"PROSHKA_CHANNEL_DESTINATION_ESCAPE:{DESTINATION}")

    sources = selected_sources()
    by_name: dict[str, Path] = {}
    for source in sources:
        previous = by_name.get(source.name)
        if previous is not None and previous != source:
            raise RuntimeError(
                f"PROSHKA_CHANNEL_FLAT_NAME_COLLISION:"
                f"{source.name}:{previous}:{source}"
            )
        by_name[source.name] = source

    DESTINATION.mkdir(parents=True, exist_ok=True)
    channel_rule = DESTINATION / "CHANNEL_RULE.md"
    manifest = DESTINATION / "MANIFEST.md"
    allowed_names = set(by_name) | {channel_rule.name, manifest.name}
    for existing in DESTINATION.iterdir():
        if not existing.is_file():
            raise RuntimeError(
                f"PROSHKA_CHANNEL_NONFLAT_DESTINATION:{existing}"
            )
        if existing.name not in allowed_names:
            existing.unlink()

    for name, source in by_name.items():
        shutil.copy2(source, DESTINATION / name)

    source_commit = git_output("rev-parse", "HEAD")
    channel_rule.write_text(
        "# Proshka GitHub channel\n\n"
        "This directory is the flat outbound Route B mirror for Proshka.\n\n"
        "Permanent handoff rule: after every closed Route B goal, refresh this "
        "mirror, rebuild `MANIFEST.md`, commit only `docs/routeB_bus/`, and "
        "push the current canonical-repository branch. Bus 010 remains void "
        "unless the owner explicitly creates it.\n\n"
        f"Source repository commit at refresh: `{source_commit}`.\n",
        encoding="utf-8",
    )

    mirrored = sorted(
        (DESTINATION / name for name in by_name),
        key=lambda path: path.name,
    )
    listed = mirrored + [channel_rule]
    lines = [
        "# Route B bus mirror manifest",
        "",
        (
            f"Flat Proshka mirror from `rh_lean_01_2026`; "
            f"{len(mirrored)} mirrored source files plus `CHANNEL_RULE.md`."
        ),
        "",
        "| File | Description | SHA-256 |",
        "|---|---|---|",
    ]
    for path in listed:
        description = (
            "channel handoff discipline"
            if path == channel_rule
            else role(by_name[path.name])
        )
        lines.append(f"| `{path.name}` | {description} | `{sha256(path)}` |")
    lines.extend(
        [
            "",
            "`MANIFEST.md` is excluded from its own hash table.",
            "",
        ]
    )
    manifest.write_text("\n".join(lines), encoding="utf-8")

    print(f"PROSHKA_CHANNEL_MIRRORED_SOURCES={len(mirrored)}")
    print(f"PROSHKA_CHANNEL_FILES_WITH_METADATA={len(listed) + 1}")
    print(f"PROSHKA_CHANNEL_MANIFEST={manifest}")


if __name__ == "__main__":
    main()
