from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "root_archive_moves", ROOT / "orchestrator/root_archive_moves.py"
)
assert SPEC and SPEC.loader
pm = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(pm)


@pytest.fixture(scope="session")
def full_receipt() -> dict:
    return pm.build_receipt()


def test_final_candidate_is_exact_postmove_tree(full_receipt: dict) -> None:
    receipt = full_receipt
    tree = receipt["prospective_tree_excluding_receipt"]
    pm.verify_candidate_scope(tree)
    pm.verify_move_invariants(tree)
    pm.verify_portable_tree(tree)
    assert receipt["active_consumer_count"] == 0
    assert len(receipt["cohort"]) == 5


def test_final_executable_control_reference_blocks(tmp_path: Path) -> None:
    with pytest.raises(pm.ArchiveMoveError, match="P9_ACTIVE_OR_UNTYPED_REFERENCE"):
        pm.raw_occurrence_inventory(
            "synthetic",
            [("docs/semantic_quarantine/executable_control_plant.py", "0" * 40, b'open("run.jsonl").read()\n')],  # P9_PLANT
        )


def test_final_raw_binary_reference_blocks(tmp_path: Path) -> None:
    with pytest.raises(pm.ArchiveMoveError, match="P9_ACTIVE_OR_UNTYPED_REFERENCE"):
        pm.raw_occurrence_inventory(
            "synthetic",
            [("docs/generated/p9-binary-plant.bin", "0" * 40, b"\x00\xffrun.jsonl\x00")],  # P9_PLANT
        )


@pytest.mark.parametrize(
    "body",
    [
        b"import louise_last_response  # P9_PLANT\n",
        b"import louise.last.response  -- P9_PLANT\n",
        b"generated = 'louise-last-response.md'  # P9_PLANT\n",
        b"encoded = '%2Ecodex_browser_snapshot_proshka%2Emd'  # P9_PLANT\n",
        b"upper = 'LOUISE-LAST-RESPONSE.MD'  # P9_PLANT\n",
    ],
)
def test_final_stem_generated_url_and_case_variants_block(tmp_path: Path, body: bytes) -> None:
    with pytest.raises(pm.ArchiveMoveError, match="P9_ACTIVE_OR_UNTYPED_REFERENCE"):
        pm.raw_occurrence_inventory(
            "synthetic", [("docs/generated/p9-variant-plant.py", "0" * 40, body)]
        )


@pytest.mark.parametrize(
    ("path", "body", "mode"),
    [
        ("scripts/p9-selector-plant.py", b"for f in *; do echo $f; done  # P9_PLANT\n", "100644"),
        ("scripts/p9-selector-plant.py", b"find . -name '*.jsonl'  # P9_PLANT\n", "100644"),
        ("scripts/p9-selector-plant.py", b"from pathlib import Path\nfor p in Path.cwd().glob('*.jsonl'): pass  # P9_PLANT\n", "100644"),
        ("scripts/p9-selector-plant", b"#!/bin/sh\nfor f in *; do echo $f; done  # P9_PLANT\n", "100755"),
    ],
)
def test_final_root_enumeration_blocks(
    tmp_path: Path, path: str, body: bytes, mode: str
) -> None:
    line = next(value for value in body.decode().splitlines() if value and not value.startswith("#!"))
    role, blocks = pm.selector_decision(path, line, mode, {path} if body.startswith(b"#!") else set())
    assert role == "UNCLASSIFIED_ROOT_SELECTOR"
    assert blocks is True


def test_final_destination_byte_mode_and_source_resurrection_block(tmp_path: Path) -> None:
    base = pm.prospective_tree(pm.support_objects())
    target = pm.COHORT["run.jsonl"]  # P9_TYPED_TEST
    byte_drift = mutate_tree(tmp_path, base, target, b"drift\n")
    with pytest.raises(pm.ArchiveMoveError, match="P9_TARGET_OBJECT_DRIFT"):
        pm.verify_move_invariants(byte_drift)
    mode_drift = mutate_tree(tmp_path, base, target, pm.tree_blob(base, target), mode="100755")
    with pytest.raises(pm.ArchiveMoveError, match="P9_TARGET_OBJECT_DRIFT"):
        pm.verify_move_invariants(mode_drift)
    resurrected = mutate_tree(tmp_path, base, "run.jsonl", b"../target", mode="120000")  # P9_TYPED_TEST
    with pytest.raises(pm.ArchiveMoveError, match="P9_SOURCE_RESURRECTED"):
        pm.verify_move_invariants(resurrected)


def test_final_portable_casefold_collision_blocks(tmp_path: Path) -> None:
    base = pm.prospective_tree(pm.support_objects())
    collision = mutate_tree(
        tmp_path,
        base,
        "ARCHIVE/root_artifacts/provenance/run.jsonl",  # P9_TYPED_TEST
        b"collision",
    )
    with pytest.raises(pm.ArchiveMoveError, match="P9_PORTABLE_COLLISION"):
        pm.verify_portable_tree(collision)
    nfd_path = "docs/p9-" + "é".encode().decode().replace("é", "e\u0301") + ".txt"
    nfd = mutate_tree(tmp_path, base, nfd_path, b"nfd")
    with pytest.raises(pm.ArchiveMoveError, match="P9_PORTABLE_NFC_PATH"):
        pm.verify_portable_tree(nfd)


def test_final_target_duplicate_prefix_and_symlink_parent_block(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    duplicate = dict(pm.COHORT)
    duplicate["louise-last-response.md"] = duplicate["run.jsonl"]  # P9_TYPED_TEST
    monkeypatch.setattr(pm, "COHORT", duplicate)
    with pytest.raises(pm.ArchiveMoveError, match="P9_TARGET_DUPLICATE"):
        pm.validate_mapping()
    monkeypatch.undo()
    prefix = dict(pm.COHORT)
    prefix["louise-last-response.md"] = prefix["run.jsonl"] + "/louise-last-response.md"  # P9_TYPED_TEST
    monkeypatch.setattr(pm, "COHORT", prefix)
    with pytest.raises(pm.ArchiveMoveError, match="P9_TARGET_PREFIX_COLLISION"):
        pm.validate_mapping()
    monkeypatch.undo()
    (tmp_path / "archive").symlink_to(tmp_path / "elsewhere", target_is_directory=True)
    with pytest.raises(pm.ArchiveMoveError, match="P9_TARGET_PARENT_SYMLINK"):
        pm.validate_destination_parents(tmp_path, "archive/root_artifacts/provenance/run.jsonl")  # P9_TYPED_TEST


def test_final_foreign_drift_and_rollback_mapping_are_exact(
    full_receipt: dict, monkeypatch: pytest.MonkeyPatch
) -> None:
    receipt = full_receipt
    expected = receipt["foreign_dirty_snapshot"]
    monkeypatch.setattr(pm, "foreign_dirty_snapshot", lambda: expected + [{"path": "plant"}])
    with pytest.raises(pm.ArchiveMoveError, match="P9_FOREIGN_DIRTY_DRIFT"):
        pm.verify_foreign_snapshot(expected)
    assert receipt["rollback_mapping"] == [
        {"from": target, "to": source, "git_operation": "git mv"}
        for source, target in sorted(pm.COHORT.items())
    ]


def test_execute_rolls_back_real_moves_after_postmove_gate_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    clone_env = os.environ.copy()
    clone_env["GIT_LFS_SKIP_SMUDGE"] = "1"
    origin = tmp_path / "origin.git"
    subprocess.run(
        ["git", "clone", "--quiet", "--bare", "--shared", str(ROOT), str(origin)],
        env=clone_env,
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(origin), "update-ref", "refs/heads/rh_clean", pm.BASELINE_COMMIT],
        check=True,
    )
    clone = tmp_path / "rollback-clone"
    subprocess.run(
        [
            "git",
            "clone",
            "--quiet",
            "--shared",
            "--no-checkout",
            str(origin),
            str(clone),
        ],
        env=clone_env,
        check=True,
    )
    subprocess.run(
        [
            "git",
            "-C",
            str(clone),
            "-c",
            "filter.lfs.process=",
            "-c",
            "filter.lfs.smudge=",
            "-c",
            "filter.lfs.required=false",
            "checkout",
            "--quiet",
            pm.BASELINE_COMMIT,
        ],
        env=clone_env,
        check=True,
    )
    for source in (
        pm.CHECKER,
        pm.TESTS,
        pm.WRAPPER,
        pm.P8_CHECKER,
        pm.P8_TESTS,
        pm.P7_CHECKER,
        pm.P7_TESTS,
    ):
        target = clone / source.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)

    spec = importlib.util.spec_from_file_location(
        "root_archive_moves_rollback_clone", clone / "orchestrator/root_archive_moves.py"
    )
    assert spec and spec.loader
    clone_pm = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(clone_pm)
    clone_pm.write_support_artifacts()

    foreign_path = clone / "README.md"
    foreign_before = foreign_path.read_bytes() + b"\nP9 rollback foreign-byte plant\n"
    foreign_path.write_bytes(foreign_before)
    receipt = clone_pm.build_receipt()
    clone_pm.write_json(clone_pm.RECEIPT, receipt)
    clone_pm.write_json(clone_pm.UMBRELLA, clone_pm.execution_umbrella(receipt))

    source_state = {
        source: (clone / source).read_bytes() for source in clone_pm.COHORT
    }
    original_gate = clone_pm.verify_move_invariants
    gate_calls = 0

    def fail_second_move_invariant_check(treeish: str) -> None:
        nonlocal gate_calls
        gate_calls += 1
        original_gate(treeish)
        if gate_calls == 2:
            raise clone_pm.ArchiveMoveError("P9_ROLLBACK_POSTMOVE_PLANT")

    monkeypatch.setattr(clone_pm, "verify_move_invariants", fail_second_move_invariant_check)
    with pytest.raises(clone_pm.ArchiveMoveError, match="P9_ROLLBACK_POSTMOVE_PLANT"):
        clone_pm.execute_moves(receipt)
    assert gate_calls == 2

    for source, target in clone_pm.COHORT.items():
        assert (clone / source).read_bytes() == source_state[source]
        assert not (clone / target).exists()
    assert foreign_path.read_bytes() == foreign_before
    staged_tree = subprocess.check_output(
        ["git", "-C", str(clone), "write-tree"], text=True
    ).strip()
    baseline_tree = subprocess.check_output(
        ["git", "-C", str(clone), "rev-parse", f"{clone_pm.BASELINE_COMMIT}^{{tree}}"],
        text=True,
    ).strip()
    assert staged_tree == baseline_tree
    subprocess.run(
        [
            "git",
            "-C",
            str(clone),
            "diff",
            "--cached",
            "--exit-code",
            clone_pm.BASELINE_COMMIT,
            "--",
        ],
        check=True,
    )
    assert subprocess.check_output(
        ["git", "-C", str(clone), "ls-tree", "-r", baseline_tree]
    ) == subprocess.check_output(
        ["git", "-C", str(clone), "ls-tree", "-r", staged_tree]
    )


def test_final_history_self_refs_nonblock_and_p7_provenance_preserved(
    full_receipt: dict,
) -> None:
    receipt = full_receipt
    roles = {row["role"] for row in receipt["occurrences"]}
    assert "P8_V1_IMMUTABLE_PREDECESSOR_ROW" in roles
    assert "P9_EXACT_MAPPING_OR_TYPED_SCANNER_LITERAL" in roles
    successor = json.loads(pm.P7_SUCCESSOR.read_text())
    relocation = successor["relocations"][0]
    assert relocation["original_row"]["sha256"] == relocation["successor_row"]["sha256"]


def mutate_tree(tmp_path: Path, base: str, path: str, data: bytes, mode: str = "100644") -> str:
    index = tmp_path / (path.replace("/", "_") + ".index")
    env = os.environ.copy()
    env["GIT_INDEX_FILE"] = str(index)
    subprocess.run(["git", "-C", str(ROOT), "read-tree", base], env=env, check=True)
    oid = (
        subprocess.check_output(
            ["git", "-C", str(ROOT), "hash-object", "-w", "--stdin"], input=data
        )
        .decode()
        .strip()
    )
    subprocess.run(
        ["git", "-C", str(ROOT), "update-index", "--add", "--cacheinfo", mode, oid, path],
        env=env,
        check=True,
    )
    return subprocess.check_output(
        ["git", "-C", str(ROOT), "write-tree"], env=env, text=True
    ).strip()
