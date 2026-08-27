from __future__ import annotations

import importlib.util
import json
import os
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "portability_manifest", ROOT / "orchestrator/portability_manifest.py"
)
assert SPEC and SPEC.loader
pm = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(pm)


def test_inventory_is_schema_valid_and_complete() -> None:
    inventory = pm.build_inventory()
    pm.validate_shape(inventory)
    assert len(inventory["active_clean_paths"]) == 24
    assert len(inventory["symlinks"]) == 35


def test_active_paths_are_clean() -> None:
    for path in pm.ACTIVE_CLEAN_PATHS:
        assert pm.hit_ids(pm.effective_bytes(path)) == []


def test_manifest_matches_effective_tracked_bytes() -> None:
    manifest = json.loads(pm.MANIFEST.read_text())
    pm.verify(manifest)


def test_active_absolute_and_stale_plants() -> None:
    assert "HOME_USERS" in pm.hit_ids(pm.PATTERNS["HOME_USERS"] + b"x")
    assert "STALE_REPO_MAC" in pm.hit_ids(pm.PATTERNS["STALE_REPO_MAC"])


def test_unclassified_or_omitted_baseline_is_detected() -> None:
    manifest = pm.build_inventory()
    assert manifest["historical_hits"]
    manifest["historical_hits"] = manifest["historical_hits"][1:]
    with pytest.raises(pm.PortabilityError, match="INVENTORY_INCOMPLETE"):
        pm.verify(manifest)


def test_route_state_locator_is_repo_relative_and_has_no_consumers() -> None:
    inventory = pm.build_inventory()
    row = next(
        row
        for row in inventory["active_clean_paths"]
        if row["path"].endswith("ROUTE_B_EXECUTION_STATE.json")
    )
    assert row["repo_relative_to"] == "GIT_TOPLEVEL"
    assert row["canonical_repo_path_consumer_count"] == 0
    state = json.loads((ROOT / row["path"]).read_text())
    assert state["canonical_repo_path"] == "."


def test_historical_promoted_active_is_detected(monkeypatch: pytest.MonkeyPatch) -> None:
    path = pm.ACTIVE_CLEAN_PATHS[0]
    original = pm.effective_bytes
    monkeypatch.setattr(
        pm, "effective_bytes", lambda p: pm.PATTERNS["MOUNT_ROOT"] if p == path else original(p)
    )
    with pytest.raises(pm.PortabilityError, match="ACTIVE_PATH_NOT_PORTABLE"):
        pm.build_inventory()


@pytest.mark.parametrize(
    ("target", "code"),
    [
        (str(ROOT / "README.md"), "ABSOLUTE_SYMLINK"),
        ("../../../../../../outside", "ESCAPING_SYMLINK"),
        ("not-a-real-target", "BROKEN_SYMLINK"),
    ],
)
def test_bad_symlink_plants(target: str, code: str) -> None:
    with pytest.raises(pm.PortabilityError, match=code):
        pm.resolved_link("q3.lean.aristotle/ACTIVE/refs/plant", target)


def test_staged_symlink_plant_reaches_scanner() -> None:
    with pytest.raises(pm.PortabilityError, match="ABSOLUTE_SYMLINK"):
        pm.staged_symlink_plant(pm.PATTERNS["HOME_USERS"].decode() + "plant/target")


def test_staged_scope_plant_rejects_outside_path_in_private_real_index() -> None:
    with pytest.raises(pm.PortabilityError, match="P7_STAGED_SCOPE_DRIFT"):
        pm.staged_scope_plant()


def test_systemd_locator_accepts_gitfiles_not_only_dot_git_directories() -> None:
    unit = (ROOT / "specs_docs/systemd/q3-attestation-broker.service").read_text()
    assert "rev-parse --show-toplevel" in unit
    assert "realpath" in unit
    assert 'test -d "$${Q3_REPO}/.git"' not in unit
    assert 'test -f "$${ROOT}/docs/CODEX_CONTROL.md"' in unit
    assert 'test -f "$${ROOT}/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md"' in unit
    assert 'test -f "$${ROOT}/q3.lean.aristotle/lakefile.toml"' in unit


def test_hook_positive_path_executes_in_canonical_repo() -> None:
    result = subprocess.run(
        ["bash", "specs_docs/hooks/q3-toolbelt.sh"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=15,
        check=False,
    )
    assert result.returncode == 0
    assert "Q3" in result.stdout
    assert "пояс с инструментами" in result.stdout


def test_hook_uses_q3_repo_from_outside_checkout(tmp_path: Path) -> None:
    env = os.environ.copy()
    env["Q3_REPO"] = str(ROOT)
    result = subprocess.run(
        ["bash", str(ROOT / "specs_docs/hooks/q3-toolbelt.sh")],
        cwd=tmp_path,
        env=env,
        text=True,
        capture_output=True,
        timeout=15,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert "Q3" in result.stdout


def test_systemd_validation_prefix_executes_in_canonical_repo() -> None:
    unit = (ROOT / "specs_docs/systemd/q3-attestation-broker.service").read_text()
    line = next(line for line in unit.splitlines() if line.startswith("ExecStart="))
    command = line.split(" -c ", 1)[1]
    assert command.startswith("'") and command.endswith("'")
    command = command[1:-1].replace("$$", "$")
    command = command.replace(
        "exec .venv/bin/python orchestrator/semantic_attestation_broker.py", "true"
    )
    env = os.environ.copy()
    env["Q3_REPO"] = str(ROOT)
    result = subprocess.run(
        ["/bin/sh", "-c", command],
        cwd=ROOT,
        env=env,
        text=True,
        capture_output=True,
        timeout=10,
        check=False,
    )
    assert result.returncode == 0, result.stderr


def test_receipt_provenance_survives_own_postcommit_head() -> None:
    receipt = pm.receipt(json.loads(pm.MANIFEST.read_text()))
    synthetic_head = subprocess.check_output(
        [
            "git",
            "-C",
            str(ROOT),
            "commit-tree",
            receipt["prospective_tree_excluding_receipt"],
            "-p",
            receipt["source_commit"],
            "-m",
            "P7 prospective postcommit provenance test",
        ],
        text=True,
    ).strip()
    pm.verify_receipt_provenance(receipt, head=synthetic_head)
    assert (
        pm.receipt(json.loads(pm.MANIFEST.read_text()), receipt)["source_commit"]
        == receipt["source_commit"]
    )


def test_stale_precommit_receipt_is_rejected_but_postcommit_ancestor_is_allowed() -> None:
    payload = json.loads(pm.RECEIPT.read_text())
    with pytest.raises(pm.PortabilityError, match="PORTABILITY_PRECOMMIT_PROVENANCE_STALE"):
        pm.verify_precommit_provenance(payload, dirty=True, current_head="f" * 40)
    pm.verify_precommit_provenance(payload, dirty=False, current_head="f" * 40)


def test_dirty_precommit_requires_fresh_prospective_tree(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = pm.receipt(json.loads(pm.MANIFEST.read_text()))
    monkeypatch.setattr(pm, "prospective_tree", lambda: "0" * 40)
    with pytest.raises(pm.PortabilityError, match="PORTABILITY_PRECOMMIT_CANDIDATE_TREE_STALE"):
        pm.verify_precommit_provenance(payload, dirty=True, current_head=pm.CURRENT_HEAD)


def test_freeze_head_window_rejects_mid_write_head_advance(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    old = "1" * 40
    new = "2" * 40
    heads = iter((old, new))
    monkeypatch.setattr(pm, "live_head", lambda: next(heads))
    monkeypatch.setattr(pm, "origin_head", lambda: old)
    assert pm.assert_freeze_head(old) == old
    with pytest.raises(pm.PortabilityError, match="P7_FREEZE_HEAD_ORIGIN_DRIFT"):
        pm.assert_freeze_head(old)


def test_descendant_new_nonmanaged_hit_is_rejected_without_staged_drift(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    oid = (
        subprocess.check_output(
            ["git", "-C", str(ROOT), "hash-object", "-w", "--stdin"],
            input=pm.PATTERNS["MOUNT_ROOT"] + b"new-machine-path\n",
        )
        .decode()
        .strip()
    )
    index = tmp_path / "index"
    env = os.environ.copy()
    env["GIT_INDEX_FILE"] = str(index)
    subprocess.run(["git", "-C", str(ROOT), "read-tree", pm.CURRENT_HEAD], env=env, check=True)
    subprocess.run(
        [
            "git",
            "-C",
            str(ROOT),
            "update-index",
            "--add",
            "--cacheinfo",
            "100644",
            oid,
            "docs/new-unclassified-machine-path.md",
        ],
        env=env,
        check=True,
    )
    tree = subprocess.check_output(
        ["git", "-C", str(ROOT), "write-tree"], env=env, text=True
    ).strip()
    descendant = subprocess.check_output(
        ["git", "-C", str(ROOT), "commit-tree", tree, "-p", pm.CURRENT_HEAD, "-m", "plant"],
        text=True,
    ).strip()
    subprocess.run(["git", "-C", str(ROOT), "read-tree", descendant], env=env, check=True)
    monkeypatch.setattr(pm, "CURRENT_HEAD", descendant)
    pm.head_snapshot.cache_clear()
    try:
        with pytest.raises(pm.PortabilityError, match="INVENTORY_INCOMPLETE"):
            pm.verify(json.loads(pm.MANIFEST.read_text()))
        pm.check_staged_scope(index)
    finally:
        pm.head_snapshot.cache_clear()


def test_machine_registry_rejects_same_pattern_outside_paths() -> None:
    source = (ROOT / "docs/cartographer/lean_bases.yaml").read_text()
    poisoned = source.replace(
        "origin: https://github.com/anthropics/zeta-23-lean.git",
        "origin: " + pm.PATTERNS["MOUNT_ROOT"].decode() + "forbidden-origin",
        1,
    )
    with pytest.raises(
        pm.PortabilityError, match="MACHINE_LOCAL_REGISTRY_HIT_OUTSIDE_ALLOWED_FIELD"
    ):
        pm.validate_machine_local_registry("docs/cartographer/lean_bases.yaml", poisoned.encode())


def test_append_history_anchor_and_first_parent_chain_are_verified() -> None:
    path = "docs/routeB_bus/PROSHKA_QUEUE.md"
    data = pm.effective_bytes(path)
    row = pm.validate_append_history_surface(path, data)
    assert row["validation"] == "FIRST_PARENT_FULL_BYTE_PREFIX_CHAIN_ANCHORED_AT_FREEZE"
    anchor = pm.queue_anchor()
    pm.verify_append_history_anchor(anchor, worktree_bytes=data + b"\nappend-only plant\n")


def test_append_history_rejects_shortening_and_internal_rewrite() -> None:
    baseline = b"full immutable queue bytes\n"
    with pytest.raises(pm.PortabilityError, match="APPEND_HISTORY_SHORTENED"):
        pm.validate_full_byte_prefix_chain([baseline, baseline[:-1]])
    rewritten = b"X" + baseline[1:] + b"appended\n"
    with pytest.raises(pm.PortabilityError, match="APPEND_HISTORY_BYTE_REWRITE"):
        pm.validate_full_byte_prefix_chain([baseline, rewritten])


def test_candidate_tree_rejects_claimed_blob_hash_mismatch() -> None:
    manifest = json.loads(pm.MANIFEST.read_text())
    payload = pm.receipt(manifest)
    payload["hashes"]["tests"] = "0" * 64
    with pytest.raises(pm.PortabilityError, match="PORTABILITY_CANDIDATE_TREE_HASH_MISMATCH:tests"):
        pm.verify_candidate_tree(payload)


def test_candidate_tree_rejects_missing_required_changed_path(tmp_path: Path) -> None:
    payload = pm.receipt(json.loads(pm.MANIFEST.read_text()))
    path = "docs/HEAVY_BUILD_RUNBOOK.md"
    source_entry = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-tree", payload["source_commit"], "--", path],
        text=True,
    ).split()
    index = tmp_path / "index"
    env = os.environ.copy()
    env["GIT_INDEX_FILE"] = str(index)
    subprocess.run(
        ["git", "-C", str(ROOT), "read-tree", payload["prospective_tree_excluding_receipt"]],
        env=env,
        check=True,
    )
    subprocess.run(
        [
            "git",
            "-C",
            str(ROOT),
            "update-index",
            "--cacheinfo",
            source_entry[0],
            source_entry[2],
            path,
        ],
        env=env,
        check=True,
    )
    weakened = subprocess.check_output(
        ["git", "-C", str(ROOT), "write-tree"], env=env, text=True
    ).strip()
    payload["prospective_tree_excluding_receipt"] = weakened
    with pytest.raises(pm.PortabilityError, match="PORTABILITY_CANDIDATE_TREE_EXACT_SCOPE_DRIFT"):
        pm.verify_candidate_tree(payload)


def test_wrapper_missing_and_nonexec_preconditions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = pm.build_inventory()
    missing = tmp_path / "missing"
    monkeypatch.setattr(pm, "WRAPPER", missing)
    with pytest.raises(pm.PortabilityError, match="WRAPPER_MISSING"):
        pm.verify(manifest)
    missing.write_text("#!/bin/sh\n")
    with pytest.raises(pm.PortabilityError, match="WRAPPER_NOT_EXECUTABLE"):
        pm.verify(manifest)
