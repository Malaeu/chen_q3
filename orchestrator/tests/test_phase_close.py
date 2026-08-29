from __future__ import annotations

import sqlite3
import tempfile
import unittest
from pathlib import Path

from specs_docs import phase_close


class PhaseClosePlants(unittest.TestCase):
    def test_gate_stops_after_first_failure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            gates = []
            for name, code in (("a.sh", 0), ("b.sh", 7), ("c.sh", 0)):
                path = root / name
                path.write_text(f"#!/bin/sh\nexit {code}\n")
                gates.append(path)
            self.assertEqual(phase_close.run_gates(root, gates), [(str(gates[0]), 0), (str(gates[1]), 7)])

    def test_assembly_debt_has_addresses_and_insight_is_visible(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            db = Path(tmp) / "knowledge.db"
            with sqlite3.connect(db) as conn:
                conn.execute("CREATE TABLE assembly(chain TEXT, step INTEGER, status TEXT)")
                conn.executemany("INSERT INTO assembly VALUES(?,?,?)", [("A", 2, "OPEN"), ("B", 1, "READY")])
            self.assertEqual(phase_close.assembly_debt(db), ["A:2:OPEN"])
            debt = phase_close.manual_debt(statuses=[], assembly=["A:2:OPEN"], owned_paths=["x"], insight_receipt=None)
            self.assertEqual(debt["insight_required"], ["INSIGHT_REQUIRED_FOR_CHANGED_SCOPE"])


if __name__ == "__main__":
    unittest.main()
