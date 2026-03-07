#!/usr/bin/env python3
from __future__ import annotations

import runpy
import sys
from pathlib import Path


ROOT_SCRIPT = Path(__file__).resolve().parents[2] / "scripts" / "research_oracle.py"


def main() -> None:
    if not ROOT_SCRIPT.exists():
        raise SystemExit(f"Missing backend script: {ROOT_SCRIPT}")
    sys.path.insert(0, str(ROOT_SCRIPT.parent))
    runpy.run_path(str(ROOT_SCRIPT), run_name="__main__")


if __name__ == "__main__":
    main()
