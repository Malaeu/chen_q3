#!/bin/sh
# Portable entry (Linux + macOS): the logic lives in scripts/phase_end.py.
here="$(cd "$(dirname "$0")/.." && pwd)"
py="$here/.venv/bin/python"; [ -x "$py" ] || py="python3"
exec "$py" "$here/scripts/phase_end.py" "$@"
