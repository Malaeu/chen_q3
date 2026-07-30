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
GOAL_033_REQUIRED_SOURCES = (
    REQUEST_DIR / "033_full_window_positive_part.goal.md",
    REQUEST_DIR / "033_full_window_positive_part.answer.md",
    REQUEST_DIR / "FULL_WINDOW_POSITIVE_PART_CERT.json",
    REQUEST_DIR / "full_window_positive_part_certificate.py",
    REQUEST_DIR / "check_full_window_positive_part_certificate.py",
    REQUEST_DIR / "FULL_WINDOW_BAND_PROFILE.csv",
    REQUEST_DIR / "FULL_WINDOW_TOOTH_LEDGER.csv",
    REQUEST_DIR / "proshka" / "PROSHKA_033_DIRECTIVE_2026-07-29.md",
)
GOAL_034_REQUIRED_SOURCES = (
    REQUEST_DIR / "034_cofinal_scaled_edge_sliver_moment.answer.md",
    REQUEST_DIR / "034_edge_sliver_REGISTRATION.md",
    REQUEST_DIR / "034_edge_sliver_INBOX_COVER.md",
    REQUEST_DIR / "check_034_edge_sliver_reduction.py",
    REQUEST_DIR / "CHECK_034_RUN.log",
    REQUEST_DIR / "ARISTOTLE_TASK_EdgeSliverMomentReduction.md",
    REQUEST_DIR
    / "ARISTOTLE_TASK_EStarMuntzContinuation_v3_PoleSubtracted.md",
    REQUEST_DIR / "proshka" / "PROSHKA_033_AND_MUNTZ_POLE_SUBTRACTED_v2.md",
    REQUEST_DIR / "proshka" / "PROSHKA_034_EDGE_SLIVER_CONTRACT.md",
)
GOAL_035_REQUIRED_SOURCES = (
    REQUEST_DIR / "035_edge_sliver_materialization.goal.md",
    REQUEST_DIR / "035_edge_sliver_materialization.answer.md",
    REQUEST_DIR / "036_tooth_sign.goal.md",
    REQUEST_DIR / "CHECK_035_REPLAY.log",
    REQUEST_DIR / "P1_RADIUS_MUTATION.csv",
)
GOAL_037_REQUIRED_SOURCES = (
    REQUEST_DIR / "037_muntz_r6_harvest.goal.md",
    REQUEST_DIR / "037_muntz_r6_harvest.answer.md",
)
GOAL_038_REQUIRED_SOURCES = (
    REQUEST_DIR / "038_scaled_outer_sign_barrier.goal.md",
    REQUEST_DIR / "038_scaled_outer_sign_barrier.answer.md",
    REQUEST_DIR / "JACOBI_LIFT_BREAK_LIST.md",
    REQUEST_DIR / "SUPPLIER_A_REHEARSAL_M257.md",
    REQUEST_DIR / "P038_PLANT_LOG.md",
    REQUEST_DIR / "CHECK_038_RUN.log",
    REQUEST_DIR / "check_038_scaled_outer_sign_barrier.py",
)
GOAL_039_REQUIRED_SOURCES = (
    REQUEST_DIR / "039_muntz_v3_consumption.goal.md",
    REQUEST_DIR / "039_muntz_v3_consumption.answer.md",
    REQUEST_DIR / "MUNTZ_V3_CONSUMPTION_LEDGER.md",
)
MUNTZ_R6_DIR = REQUEST_DIR / "muntz_r6"
MUNTZ_R6_REQUIRED_RELATIVE_PATHS = (
    Path("_COVER.md"),
    Path("ARISTOTLE_SUMMARY.md"),
    Path("README.md"),
    Path("RESULT.md"),
    Path("RequestProject/.gitkeep"),
    Path("RequestProject/ConcreteAnalyticity.lean"),
    Path("RequestProject/IntegralAnalyticity.lean"),
    Path("RequestProject/Main.lean"),
    Path("RequestProject/PoleSubtracted.lean"),
    Path("RequestProject/RiemannBoundaryCellBridge.lean"),
    Path("RequestProject/TailAnalyticity.lean"),
    Path("RequestProject/WindowAnalyticity.lean"),
    Path("lake-manifest.json"),
    Path("lakefile.toml"),
    Path("lean-toolchain"),
)
MUNTZ_V3_DIR = REQUEST_DIR / "muntz_v3"
MUNTZ_V3_REQUIRED_RELATIVE_PATHS = (
    Path("_COVER.md"),
    Path("ARISTOTLE_SUMMARY.md"),
    Path("README.md"),
    Path("RequestProject/.gitkeep"),
    Path("RequestProject/Main.lean"),
    Path("RequestProject/MellinCompactSupportAnalyticity.lean"),
    Path("RequestProject/MuntzV3Unconditional.lean"),
    Path("lake-manifest.json"),
    Path("lakefile.toml"),
    Path("lean-toolchain"),
)
PROSHKA_SYSTEM_PROMPT = (
    REQUEST_DIR / "proshka" / "PROSHKA_SYSTEM_PROMPT_v2.md"
)

def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def role(path: Path) -> str:
    name = path.name
    if MUNTZ_R6_DIR.name in path.parts:
        if name == "_COVER.md":
            return "Muntz R6 harvest metadata"
        return "Muntz R6 harvested artifact"
    if MUNTZ_V3_DIR.name in path.parts:
        if name == "_COVER.md":
            return "Muntz v3 harvest and consumption metadata"
        if name in {
            "MellinCompactSupportAnalyticity.lean",
            "MuntzV3Unconditional.lean",
        }:
            return "Muntz v3 local Goal 039 Lean artifact"
        return "Muntz v3 harvested artifact"
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
        + GOAL_033_REQUIRED_SOURCES
        + GOAL_034_REQUIRED_SOURCES
        + GOAL_035_REQUIRED_SOURCES
        + GOAL_037_REQUIRED_SOURCES
        + GOAL_038_REQUIRED_SOURCES
        + GOAL_039_REQUIRED_SOURCES
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


def selected_nested_sources() -> dict[Path, Path]:
    paths: dict[Path, Path] = {}
    for relative in MUNTZ_R6_REQUIRED_RELATIVE_PATHS:
        source = MUNTZ_R6_DIR / relative
        if not source.is_file():
            raise FileNotFoundError(
                f"PROSHKA_CHANNEL_RESYNC_SOURCE_MISSING:{source}"
            )
        paths[Path(MUNTZ_R6_DIR.name) / relative] = source
    for relative in MUNTZ_V3_REQUIRED_RELATIVE_PATHS:
        source = MUNTZ_V3_DIR / relative
        if not source.is_file():
            raise FileNotFoundError(
                f"PROSHKA_CHANNEL_RESYNC_SOURCE_MISSING:{source}"
            )
        paths[Path(MUNTZ_V3_DIR.name) / relative] = source
    return paths


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
    nested_sources = selected_nested_sources()
    if not PROSHKA_SYSTEM_PROMPT.is_file():
        raise FileNotFoundError(
            f"PROSHKA_CHANNEL_RESYNC_SOURCE_MISSING:{PROSHKA_SYSTEM_PROMPT}"
        )
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
    nested_destinations = tuple(
        DESTINATION / name
        for name in (MUNTZ_R6_DIR.name, MUNTZ_V3_DIR.name)
    )
    proshka_destination = DESTINATION / "proshka"
    allowed_names = set(by_name) | {
        channel_rule.name,
        manifest.name,
        proshka_destination.name,
    } | {path.name for path in nested_destinations}
    for existing in DESTINATION.iterdir():
        if (
            existing in (*nested_destinations, proshka_destination)
            and existing.is_dir()
        ):
            continue
        if not existing.is_file():
            raise RuntimeError(
                f"PROSHKA_CHANNEL_NONFLAT_DESTINATION:{existing}"
            )
        if existing.name not in allowed_names:
            existing.unlink()

    for name, source in by_name.items():
        shutil.copy2(source, DESTINATION / name)

    for nested_destination in nested_destinations:
        nested_destination.mkdir(parents=True, exist_ok=True)
        allowed_nested = {
            relative.relative_to(nested_destination.name)
            for relative in nested_sources
            if relative.parts[0] == nested_destination.name
        }
        for existing in nested_destination.rglob("*"):
            if existing.is_symlink():
                raise RuntimeError(
                    f"PROSHKA_CHANNEL_NESTED_SYMLINK_FORBIDDEN:{existing}"
                )
            if existing.is_file():
                relative = existing.relative_to(nested_destination)
                if relative not in allowed_nested:
                    existing.unlink()
        for existing in sorted(
            (path for path in nested_destination.rglob("*") if path.is_dir()),
            key=lambda path: len(path.parts),
            reverse=True,
        ):
            if not any(existing.iterdir()):
                existing.rmdir()
    for relative, source in nested_sources.items():
        destination = DESTINATION / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)

    proshka_destination.mkdir(parents=True, exist_ok=True)
    prompt_destination = (
        proshka_destination / PROSHKA_SYSTEM_PROMPT.name
    )
    for existing in proshka_destination.iterdir():
        if existing == prompt_destination and existing.is_file():
            continue
        if existing.is_file():
            existing.unlink()
            continue
        raise RuntimeError(
            f"PROSHKA_CHANNEL_NESTED_NONFILE:{existing}"
        )
    shutil.copy2(PROSHKA_SYSTEM_PROMPT, prompt_destination)

    source_commit = git_output("rev-parse", "HEAD")
    channel_rule.write_text(
        "# Proshka GitHub channel\n\n"
        "This directory is the outbound Route B mirror for Proshka. Top-level "
        "artifacts are flat; source-locked subtrees are preserved only when an "
        "explicit goal requires their relative paths.\n\n"
        "Permanent handoff rule: after every closed Route B goal, refresh this "
        "mirror, rebuild `MANIFEST.md`, and push the current canonical-repository "
        "branch. Bus 010 remains void unless the owner explicitly creates it.\n\n"
        "Canon travels with the mirror (owner decision, 2026-07-30). The earlier "
        "form of this rule said *commit only* `docs/routeB_bus/`. That was "
        "followed to the letter and left the canonical bus sitting uncommitted in "
        "the working tree. Mythos reads GitHub at dispatch time, so it diagnosed "
        "from a repository state that no longer matched the disk and issued goal "
        "037 task B for a canon sync already done. Same trigger as before -- a "
        "closed goal -- but now the commit covers both the mirror and the "
        "canonical bus, so the two cannot drift apart.\n\n"
        "Still forbidden: force-push, merging `rh_clean` into `main`, any push "
        "that raises Route B status or claims RH.\n\n"
        "Каждый бриф внешнему агенту называет ветку явно: branch `rh_clean`; "
        "ссылки полные: "
        "https://github.com/Malaeu/chen_q3/tree/rh_clean/docs/routeB_bus.\n\n"
        f"Source repository commit at refresh: `{source_commit}`.\n",
        encoding="utf-8",
    )

    mirrored = sorted(
        (DESTINATION / name for name in by_name),
        key=lambda path: path.name,
    )
    nested_mirrored = [
        DESTINATION / relative for relative in sorted(nested_sources)
    ] + [prompt_destination]
    listed = sorted(
        mirrored + nested_mirrored + [channel_rule],
        key=lambda path: path.relative_to(DESTINATION).as_posix(),
    )
    source_by_destination = {
        DESTINATION / name: source for name, source in by_name.items()
    }
    source_by_destination.update(
        {
            DESTINATION / relative: source
            for relative, source in nested_sources.items()
        }
    )
    source_by_destination[prompt_destination] = PROSHKA_SYSTEM_PROMPT
    lines = [
        "# Route B bus mirror manifest",
        "",
        (
            f"Proshka mirror from `rh_lean_01_2026`; "
            f"{len(mirrored) + len(nested_mirrored)} mirrored source files "
            "plus `CHANNEL_RULE.md`."
        ),
        "",
        "| File | Description | SHA-256 |",
        "|---|---|---|",
    ]
    for path in listed:
        description = (
            "channel handoff discipline"
            if path == channel_rule
            else role(source_by_destination[path])
        )
        display_path = path.relative_to(DESTINATION).as_posix()
        lines.append(
            f"| `{display_path}` | {description} | `{sha256(path)}` |"
        )
    lines.extend(
        [
            "",
            "`MANIFEST.md` is excluded from its own hash table.",
            "",
        ]
    )
    manifest.write_text("\n".join(lines), encoding="utf-8")

    print(
        "PROSHKA_CHANNEL_MIRRORED_SOURCES="
        f"{len(mirrored) + len(nested_mirrored)}"
    )
    print(f"PROSHKA_CHANNEL_FILES_WITH_METADATA={len(listed) + 1}")
    print(f"PROSHKA_CHANNEL_MANIFEST={manifest}")


if __name__ == "__main__":
    main()
