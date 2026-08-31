from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = (
    REPO_ROOT
    / "q3.lean.aristotle"
    / "ACTIVE"
    / "requests"
    / "routeB_twolevel_spectral_ladder"
    / "routeb_status.py"
)


def load_status_module():
    spec = importlib.util.spec_from_file_location("q3_routeb_status", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_historical_marker_subscription_is_data_driven(tmp_path: Path) -> None:
    module = load_status_module()
    surface = tmp_path / "history" / "monitor.md"
    surface.parent.mkdir(parents=True)
    surface.write_text("REQUIRED HISTORICAL MARKER\n", encoding="utf-8")
    registry = tmp_path / "status_surfaces.json"
    registry.write_text(
        json.dumps(
            {
                "surfaces": [
                    {
                        "path": "history/monitor.md",
                        "role": "HISTORICAL",
                        "required_marker": "REQUIRED HISTORICAL MARKER",
                    },
                    {
                        "path": "history/unsubscribed.md",
                        "role": "HISTORICAL",
                    },
                ]
            }
        ),
        encoding="utf-8",
    )

    assert module.historical_marker_errors(tmp_path, registry) == []

    surface.write_text("marker removed\n", encoding="utf-8")
    assert module.historical_marker_errors(tmp_path, registry) == [
        "STALE_MONITOR_MISSING_HISTORICAL_MARKER:history/monitor.md"
    ]
