#!/usr/bin/env python3
"""Read-only portable verification of the historical pre-addendum gate.

Does not rerun or reinterpret any numerical result. Keep original producer
code/result hashes unchanged; resolve transported source/prediction bytes.
"""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PACKET=HERE.parent
data=json.loads((HERE/"gate.json").read_text())

def verify(expected, candidates):
    for path in candidates:
        if path.exists() and hashlib.sha256(path.read_bytes()).hexdigest()==expected:
            return str(path.relative_to(PACKET)) if path.is_relative_to(PACKET) else str(path)
    raise RuntimeError(f"NO_MATCHING_TRANSPORTED_INPUT: {expected}")

resolved={"code":verify(data["code_sha256"],[HERE/"run_gate.py"]),
          "predictions":verify(data["predictions_sha256"],[PACKET/"PREDICTIONS.md",PACKET/"producer_history/PREDICTIONS_before_addendum.md"])}
for entry in data["source_pins"]:
    name=Path(entry["path"]).name.removeprefix("corner_")
    resolved[name]=verify(entry["sha256"],[Path(entry["path"]),PACKET/"inputs"/name])
assert data["pass"] and data["positive_a_cells_passed"]==12 and data["a0_cells_passed"]==4
assert all(c["pass"] and all(r["max_abs_Q_error"]<=1e-12 for r in c["quadrature"][-2:]) for c in data["cells"])
print(json.dumps({"historical_gate_integrity":"PASS","resolved_inputs":resolved},indent=2))
