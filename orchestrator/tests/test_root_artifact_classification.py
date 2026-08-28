from __future__ import annotations

import importlib.util
import json
import os
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "root_artifact_classification", ROOT / "orchestrator/root_artifact_classification.py"
)
assert SPEC and SPEC.loader
pm = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(pm)


P8_V1_PREDECESSOR = json.loads(pm.CLASSIFICATION.read_text())["source_commit"]


@pytest.fixture(autouse=True)
def explicit_predecessor_tree_for_v1_tests(
    request: pytest.FixtureRequest, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    index = tmp_path / "phase-isolated.index"
    env = os.environ.copy()
    env["GIT_INDEX_FILE"] = str(index)
    subprocess.run(
        ["git", "-C", str(ROOT), "read-tree", pm.live_head()], env=env, check=True
    )
    monkeypatch.setenv("GIT_INDEX_FILE", str(index))
    if not request.node.name.startswith("test_v2_"):
        monkeypatch.setattr(pm, "CURRENT_HEAD", P8_V1_PREDECESSOR)
        live_collision = pm.portable_worktree_collision
        executed_targets = set(pm.P8_V2_EXECUTED_MAPPING.values())

        def predecessor_collision(root: Path, target: str) -> str | None:
            if target in executed_targets:
                return None
            return live_collision(root, target)

        monkeypatch.setattr(pm, "portable_worktree_collision", predecessor_collision)


def test_v2_transition_verifies_exact_candidate() -> None:
    pm.verify_v2_transition()


def test_v2_counts_and_executed_ledger_are_exact() -> None:
    payload = json.loads(pm.CLASSIFICATION_V2.read_text())
    assert payload["counts"] == {
        "live_root_entries": 64,
        "keep": 49,
        "archive_pending": 15,
        "executed": 5,
    }
    assert len(payload["entries"]) == 64
    assert len(payload["executed_moves"]) == 5


def test_v2_predecessor_artifacts_are_immutable() -> None:
    assert pm.sha256(pm.SCHEMA.read_bytes()) == pm.P8_V1_IMMUTABLE_HASHES["schema"]
    assert (
        pm.sha256(pm.CLASSIFICATION.read_bytes())
        == pm.P8_V1_IMMUTABLE_HASHES["classification"]
    )
    assert pm.sha256(pm.RECEIPT.read_bytes()) == pm.P8_V1_IMMUTABLE_HASHES["receipt"]


def test_v2_staged_scope_uses_live_head_not_semantic_predecessor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(pm, "CURRENT_HEAD", P8_V1_PREDECESSOR)
    pm.check_staged_scope()


def payload() -> dict:
    return pm.build_classification(P8_V1_PREDECESSOR)


def descendant(
    tmp_path: Path,
    *,
    path: str,
    data: bytes | None = None,
    mode: str = "100644",
    remove: bool = False,
) -> str:
    index = tmp_path / (path.replace("/", "_") + ".index")
    env = os.environ.copy()
    env["GIT_INDEX_FILE"] = str(index)
    subprocess.run(["git", "-C", str(ROOT), "read-tree", pm.CURRENT_HEAD], env=env, check=True)
    if remove:
        subprocess.run(
            ["git", "-C", str(ROOT), "update-index", "--force-remove", "--", path],
            env=env,
            check=True,
        )
    else:
        assert data is not None
        existing_type = subprocess.run(
            ["git", "-C", str(ROOT), "cat-file", "-t", f"{pm.CURRENT_HEAD}:{path}"],
            text=True,
            capture_output=True,
            check=False,
        )
        if existing_type.returncode == 0 and existing_type.stdout.strip() == "tree":
            subprocess.run(
                ["git", "-C", str(ROOT), "rm", "-r", "--cached", "--", path],
                env=env,
                check=True,
                stdout=subprocess.DEVNULL,
            )
        oid = (
            subprocess.check_output(
                ["git", "-C", str(ROOT), "hash-object", "-w", "--stdin"], input=data
            )
            .decode()
            .strip()
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(ROOT),
                "update-index",
                "--add",
                "--cacheinfo",
                mode,
                oid,
                path,
            ],
            env=env,
            check=True,
        )
    tree = subprocess.check_output(
        ["git", "-C", str(ROOT), "write-tree"], env=env, text=True
    ).strip()
    return subprocess.check_output(
        ["git", "-C", str(ROOT), "commit-tree", tree, "-p", pm.CURRENT_HEAD, "-m", "P8 plant"],
        text=True,
    ).strip()


def mutate_tree(
    tmp_path: Path, base_tree: str, path: str, data: bytes, mode: str = "100644"
) -> str:
    index = tmp_path / ("candidate_" + path.replace("/", "_") + ".index")
    env = os.environ.copy()
    env["GIT_INDEX_FILE"] = str(index)
    subprocess.run(["git", "-C", str(ROOT), "read-tree", base_tree], env=env, check=True)
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


def test_live_inventory_is_exhaustive_69_rows() -> None:
    data = payload()
    assert len(data["entries"]) == 69
    assert sum(row["object_kind"] == "tree" for row in data["entries"]) == 21
    assert sum(row["classification"] == "KEEP" for row in data["entries"]) == 49
    assert sum(row["classification"] == "ARCHIVE" for row in data["entries"]) == 20
    assert {row["path"] for row in data["entries"] if row["classification"] == "ARCHIVE"} == set(
        pm.ARCHIVE_PATHS
    )


def test_schema_and_source_snapshot_are_exact() -> None:
    data = payload()
    pm.validate_schema(data)
    pm.verify_source_snapshot(data)
    pm.validate_targets(data)


def test_keep_blob_content_churn_passes(tmp_path: Path) -> None:
    child = descendant(tmp_path, path="README.md", data=b"content-only descendant\n")
    pm.verify_live_classification(payload(), child)


def test_keep_tree_inner_churn_passes(tmp_path: Path) -> None:
    child = descendant(tmp_path, path="docs/p8-inner-plant.txt", data=b"inner churn\n")
    pm.verify_live_classification(payload(), child)


def test_future_session_protocol_nested_passes_but_root_fails(tmp_path: Path) -> None:
    nested = descendant(
        tmp_path,
        path="docs/session_protocols/SESSION_PROTOKOLL_2026-08-28.md",
        data=b"nested continuity protocol\n",
    )
    pm.verify_live_classification(payload(), nested)
    root = descendant(
        tmp_path,
        path="SESSION_PROTOKOLL_2026-08-28.md",
        data=b"forbidden root protocol\n",
    )
    with pytest.raises(pm.RootArtifactError, match="ROOT_SESSION_PROTOCOL_CREATION_FORBIDDEN"):
        pm.verify_live_classification(payload(), root)


@pytest.mark.parametrize(
    ("path", "mode", "data"),
    [
        ("docs/session_protocols/wrong-name.md", "100644", b"wrong name\n"),
        (
            "docs/session_protocols/SESSION_PROTOKOLL_2026-08-28.md",
            "100755",
            b"wrong mode\n",
        ),
        (
            "docs/session_protocols/SESSION_PROTOKOLL_2026-08-28.md",
            "120000",
            b"../wrong-target",
        ),
        (
            "docs/session_protocols/nested/SESSION_PROTOKOLL_2026-08-28.md",
            "100644",
            b"nested forbidden\n",
        ),
    ],
)
def test_future_session_protocol_policy_rejects_wrong_shape(
    tmp_path: Path, path: str, mode: str, data: bytes
) -> None:
    child = descendant(tmp_path, path=path, data=data, mode=mode)
    with pytest.raises(pm.RootArtifactError, match="FUTURE_SESSION_PROTOCOL_POLICY_DRIFT"):
        pm.verify_future_session_protocols(child)


def test_archive_byte_mutation_fails(tmp_path: Path) -> None:
    child = descendant(tmp_path, path="FINDINGS_SUMMARY.md", data=b"rewritten archive candidate\n")
    with pytest.raises(pm.RootArtifactError, match="ARCHIVE_DEFERRED_BYTES_DRIFT"):
        pm.verify_live_classification(payload(), child)


def test_added_and_omitted_root_entries_fail(tmp_path: Path) -> None:
    added = descendant(tmp_path, path="new-root-artifact.txt", data=b"new\n")
    with pytest.raises(pm.RootArtifactError, match="ROOT_ARTIFACT_UNCLASSIFIED"):
        pm.verify_live_classification(payload(), added)
    omitted = descendant(tmp_path, path="memo.md", remove=True)
    with pytest.raises(pm.RootArtifactError, match="ROOT_ARTIFACT_UNCLASSIFIED"):
        pm.verify_live_classification(payload(), omitted)


def test_root_kind_and_mode_drift_fail(tmp_path: Path) -> None:
    executable = descendant(tmp_path, path="README.md", data=b"mode drift\n", mode="100755")
    with pytest.raises(pm.RootArtifactError, match="ROOT_ARTIFACT_KIND_OR_MODE_DRIFT"):
        pm.verify_live_classification(payload(), executable)
    directory_to_blob = descendant(tmp_path, path="docs", data=b"kind drift\n", mode="100644")
    with pytest.raises(pm.RootArtifactError, match="ROOT_ARTIFACT_KIND_OR_MODE_DRIFT"):
        pm.verify_live_classification(payload(), directory_to_blob)


def test_root_symlink_target_drift_fails(tmp_path: Path) -> None:
    child = descendant(tmp_path, path="ACTIVE", data=b"wrong-target", mode="120000")
    with pytest.raises(pm.RootArtifactError, match="ROOT_SYMLINK_DRIFT"):
        pm.verify_live_classification(payload(), child)


def test_tracked_ignore_and_wrong_drift_matrix_fail() -> None:
    data = payload()
    ignored = json.loads(json.dumps(data))
    row = next(row for row in ignored["entries"] if row["path"] == "README.md")
    row["classification"] = "IGNORE"
    with pytest.raises(pm.RootArtifactError, match="TRACKED_IGNORE_FORBIDDEN"):
        pm.validate_targets(ignored)
    wrong = json.loads(json.dumps(data))
    row = next(row for row in wrong["entries"] if row["path"] == "README.md")
    row["drift_class"] = "ARCHIVE_DEFERRED"
    with pytest.raises(pm.RootArtifactError, match="ROOT_CLASSIFICATION_SCHEMA_INVALID"):
        pm.validate_schema(wrong)


@pytest.mark.parametrize(
    "target",
    [
        "/tmp/outside.md",
        "../outside.md",
        "archive/root_artifacts/browser_snapshots/not-the-source-basename.md",
        "FINDINGS_SUMMARY.md",
    ],
)
def test_archive_target_escape_or_mismatch_fails(target: str) -> None:
    data = payload()
    row = next(row for row in data["entries"] if row["path"] == "FINDINGS_SUMMARY.md")
    row["target"] = target
    with pytest.raises(pm.RootArtifactError, match="ARCHIVE_TARGET_COLLISION_OR_ESCAPE"):
        pm.validate_targets(data)


def test_duplicate_archive_target_fails() -> None:
    data = payload()
    rows = [row for row in data["entries"] if row["classification"] == "ARCHIVE"]
    rows[1]["target"] = rows[0]["target"]
    with pytest.raises(pm.RootArtifactError, match="ARCHIVE_TARGET_COLLISION_OR_ESCAPE"):
        pm.validate_targets(data)


def test_portable_casefold_and_nfc_target_collisions_fail() -> None:
    data = payload()
    rows = [row for row in data["entries"] if row["classification"] == "ARCHIVE"]
    rows[1]["target"] = rows[0]["target"].upper()
    with pytest.raises(pm.RootArtifactError, match="portable-duplicate"):
        pm.validate_targets(data)
    data = payload()
    row = next(row for row in data["entries"] if row["classification"] == "ARCHIVE")
    row["target"] = "archive/root_artifacts/research_notes/a\u0301.md"
    with pytest.raises(pm.RootArtifactError, match="ARCHIVE_TARGET_COLLISION_OR_ESCAPE"):
        pm.validate_targets(data)


def test_existing_target_and_ancestor_file_collision_branches_fail() -> None:
    data = payload()
    row = next(row for row in data["entries"] if row["path"] == "FINDINGS_SUMMARY.md")
    row["target"] = "README.md"
    with pytest.raises(pm.RootArtifactError, match="portable-existing"):
        pm.validate_targets(data)
    data = payload()
    row = next(row for row in data["entries"] if row["path"] == "FINDINGS_SUMMARY.md")
    row["target"] = "README.md/child.md"
    with pytest.raises(pm.RootArtifactError, match="ancestor-file"):
        pm.validate_targets(data)


def test_script_root_output_plant_and_live_scan() -> None:
    plant = b'from pathlib import Path\nPath("root-output.json").write_text("x")\n'
    assert pm.script_root_output_hits(pm.CURRENT_HEAD, "scripts/plant.py", plant) == [
        "root-output.json"
    ]
    pm.verify_script_outputs()


def test_docbuild_exception_requires_cd_before_tee_without_intervening_cd() -> None:
    reversed_order = b'lake build 2>&1 | tee docbuild.log\ncd "$DOCBUILD_DIR"\n'
    with pytest.raises(pm.RootArtifactError, match="LITERAL_SCRIPT_OUTPUT_EXCEPTION_DRIFT"):
        pm.verify_docbuild_exception(reversed_order)
    intervening = b'cd "$DOCBUILD_DIR"\ncd "$PROJECT_DIR"\nlake build | tee docbuild.log\n'
    with pytest.raises(pm.RootArtifactError, match="LITERAL_SCRIPT_OUTPUT_EXCEPTION_DRIFT"):
        pm.verify_docbuild_exception(intervening)


def test_foreign_dirty_mutation_is_detected() -> None:
    expected = pm.foreign_dirty_snapshot()
    changed = json.loads(json.dumps(expected))
    changed.append({"path": "foreign", "kind": "file", "sha256": "0" * 64, "byte_size": 0})
    with pytest.raises(pm.RootArtifactError, match="FOREIGN_DIRTY_PATH_MUTATION"):
        pm.verify_foreign_dirty_snapshot(expected, changed)


def test_foreign_dirty_mode_and_type_are_fingerprinted(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    file_path = tmp_path / "foreign-file"
    file_path.write_text("same bytes")
    directory = tmp_path / "foreign-directory"
    directory.mkdir()
    monkeypatch.setattr(pm, "ROOT", tmp_path)
    before = pm.file_fingerprint("foreign-file")
    file_path.chmod(0o755)
    after = pm.file_fingerprint("foreign-file")
    assert before["sha256"] == after["sha256"]
    assert before["mode"] != after["mode"]
    with pytest.raises(pm.RootArtifactError, match="FOREIGN_DIRTY_PATH_MUTATION"):
        pm.verify_foreign_dirty_snapshot([before], [after])
    directory_row = pm.file_fingerprint("foreign-directory")
    assert directory_row["path"] == "foreign-directory"
    assert directory_row["kind"] == "directory"
    assert directory_row["mode"] == directory.stat().st_mode & 0o7777


def test_deleted_foreign_dirty_path_has_stable_representation() -> None:
    row = pm.file_fingerprint("definitely-not-present-p8-plant")
    assert row == {"path": "definitely-not-present-p8-plant", "kind": "deleted"}


def test_portable_worktree_target_collision_detects_untracked_and_casefold(
    tmp_path: Path,
) -> None:
    target = tmp_path / "Archive" / "Root_Artifacts" / "Browser_Snapshots"
    target.mkdir(parents=True)
    (target / "Artifact.MD").write_text("untracked collision")
    assert (
        pm.portable_worktree_collision(
            tmp_path, "archive/root_artifacts/browser_snapshots/artifact.md"
        )
        == "Archive/Root_Artifacts/Browser_Snapshots/Artifact.MD"
    )


def test_candidate_tree_has_exact_p8_scope_and_no_root_semantic_diff() -> None:
    data = payload()
    receipt = pm.receipt(data)
    pm.verify_candidate_tree(receipt)


def test_candidate_tree_rejects_root_mutation(tmp_path: Path) -> None:
    data = payload()
    receipt = pm.receipt(data)
    receipt["prospective_tree_excluding_receipt"] = mutate_tree(
        tmp_path,
        receipt["prospective_tree_excluding_receipt"],
        "README.md",
        b"candidate root mutation\n",
    )
    with pytest.raises(pm.RootArtifactError, match="P8_CANDIDATE_SCOPE_DRIFT"):
        pm.verify_candidate_tree(receipt)


def test_candidate_tree_scans_new_operational_script(tmp_path: Path) -> None:
    data = payload()
    receipt = pm.receipt(data)
    checker_path = "orchestrator/root_artifact_classification.py"
    malicious = b'from pathlib import Path\nPath("candidate-root.log").write_text("x")\n'
    receipt["prospective_tree_excluding_receipt"] = mutate_tree(
        tmp_path,
        receipt["prospective_tree_excluding_receipt"],
        checker_path,
        malicious,
        mode="100755",
    )
    receipt["hashes"]["checker"] = pm.sha256(malicious)
    with pytest.raises(pm.RootArtifactError, match="LITERAL_SCRIPT_ROOT_OUTPUT_PREFLIGHT"):
        pm.verify_candidate_tree(receipt)


def test_receipt_source_cross_and_stale_tree_fail(monkeypatch: pytest.MonkeyPatch) -> None:
    data = payload()
    receipt = pm.receipt(data)
    crossed = json.loads(json.dumps(receipt))
    crossed["source_commit"] = subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", pm.CURRENT_HEAD + "^"], text=True
    ).strip()
    with pytest.raises(pm.RootArtifactError, match="P8_RECEIPT_CLASSIFICATION_SOURCE_CROSS"):
        pm.verify_receipt_provenance(crossed, data)
    monkeypatch.setattr(pm, "p8_dirty", lambda: True)
    monkeypatch.setattr(pm, "prospective_tree", lambda: "0" * 40)
    with pytest.raises(pm.RootArtifactError, match="P8_PRECOMMIT_TREE_STALE"):
        pm.verify_precommit(receipt)


def test_existing_build_never_rebaselines_archive_bytes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    baseline = payload()
    classification = tmp_path / "classification.json"
    classification.write_text(json.dumps(baseline))
    receipt_path = tmp_path / "missing-receipt.json"
    child = descendant(
        tmp_path,
        path="FINDINGS_SUMMARY.md",
        data=b"archive bytes changed before build\n",
    )
    monkeypatch.setattr(pm, "CLASSIFICATION", classification)
    monkeypatch.setattr(pm, "RECEIPT", receipt_path)
    monkeypatch.setattr(pm, "CURRENT_HEAD", child)
    before = classification.read_bytes()
    with pytest.raises(pm.RootArtifactError, match="ARCHIVE_DEFERRED_BYTES_DRIFT"):
        pm.build_or_verify()
    assert classification.read_bytes() == before


def test_existing_classification_without_receipt_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    classification = tmp_path / "classification.json"
    classification.write_text(json.dumps(payload()))
    monkeypatch.setattr(pm, "CLASSIFICATION", classification)
    monkeypatch.setattr(pm, "RECEIPT", tmp_path / "missing-receipt.json")
    with pytest.raises(pm.RootArtifactError, match="ROOT_ARTIFACT_RECEIPT_MISSING"):
        pm.build_or_verify()


def test_classification_reads_committed_root_not_dirty_worktree() -> None:
    data = payload()
    readme = next(row for row in data["entries"] if row["path"] == "README.md")
    source = pm.tree_blob(pm.CURRENT_HEAD, "README.md")
    assert readme["sha256"] == pm.sha256(source)
    assert readme["byte_size"] == len(source)
