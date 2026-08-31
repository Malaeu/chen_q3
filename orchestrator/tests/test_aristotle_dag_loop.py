from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "q3.lean.aristotle" / "scripts" / "aristotle_dag_loop.py"


def load_generator_module():
    spec = importlib.util.spec_from_file_location("q3_aristotle_dag_loop", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_generator_resolves_current_repository_layout() -> None:
    module = load_generator_module()

    assert module.ROOT == REPO_ROOT / "q3.lean.aristotle"
    assert module.REPO_ROOT == REPO_ROOT
    assert (module.REPO_ROOT / "scripts" / "build_dependency_tree.py").is_file()
    assert (module.REPO_ROOT / "scripts" / "build_proof_graph.py").is_file()


def test_sorry_scan_keeps_comment_filter_after_fast_path(tmp_path: Path) -> None:
    module = load_generator_module()
    no_sorry = tmp_path / "NoSorry.lean"
    comments_only = tmp_path / "CommentsOnly.lean"
    real_sorry = tmp_path / "RealSorry.lean"
    no_sorry.write_text("theorem clean : True := by trivial\n", encoding="utf-8")
    comments_only.write_text("-- sorry\ntheorem clean : True := by trivial\n", encoding="utf-8")
    real_sorry.write_text("theorem open_goal : True := by\n  sorry\n", encoding="utf-8")

    assert module.scan_sorries(no_sorry) == []
    assert module.scan_sorries(comments_only) == []
    assert module.scan_sorries(real_sorry) == [module.SorryInfo(line=2, decl="open_goal")]


def test_generator_excludes_q3_archive(monkeypatch, tmp_path: Path) -> None:
    module = load_generator_module()
    q3_dir = tmp_path / "Q3"
    archive_dir = q3_dir / "Archive"
    live_file = q3_dir / "Live.lean"
    archived_file = archive_dir / "Old.lean"
    archive_dir.mkdir(parents=True)
    live_file.write_text("theorem live : True := by sorry\n", encoding="utf-8")
    archived_file.write_text("theorem old : True := by sorry\n", encoding="utf-8")
    monkeypatch.setattr(module, "ARCHIVE_DIR", archive_dir)

    assert list(module.iter_lean_files([q3_dir])) == [live_file]
