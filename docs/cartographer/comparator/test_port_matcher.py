#!/usr/bin/env python3
"""T2.1 replay suite: P1-P6, NC1-NC3, C2 (+ coherent control).
PASS criteria: every expected outcome preserved; wrong-object escape = 0;
false rejection = 0 (positive controls all accepted)."""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import port_matcher as pm  # noqa: E402


def main() -> int:
    with open(os.path.join(pm.FIXTURES, "plants.json"), encoding="utf-8") as fh:
        plants = json.load(fh)
    registry = pm.load_registry()
    pre_w1 = [a for a in registry
              if a["ADAPTER_ID"] != "A_ISOMETRY_TO_AE_FOURIER_REPRESENTATIVE"]
    pairs = pm.load_adaptable_pairs()

    failures = 0
    wrong_object_escapes = 0
    false_rejections = 0
    for pid, plant in plants.items():
        if pid.startswith("_"):
            continue
        reg = pre_w1 if plant.get("registry") == "pre_w1" else registry
        if "providers" in plant:
            got, why, chain = pm.match_hyperedge(
                plant["providers"], plant["consumer_ports"], reg, pairs)
        else:
            got, why, chain = pm.match_port(
                plant["provider"], plant["consumer"], reg, pairs)
        exp = plant["expected"]
        ok = got == exp
        print(f"{pid:7s} {plant['name'][:52]:52s} expected={exp:24s} "
              f"got={got:24s} {'PASS' if ok else 'FAIL'}")
        if not ok:
            failures += 1
            print(f"        why: {why}")
            accept = ("EXACT_MATCH", "DEFINITIONAL_MATCH",
                      "EXPLICIT_ADAPTER_MATCH")
            if exp not in accept and got in accept:
                wrong_object_escapes += 1
            if exp in accept and got not in accept:
                false_rejections += 1
    print(f"FAILURES={failures} WRONG_OBJECT_ESCAPE={wrong_object_escapes} "
          f"FALSE_REJECTION={false_rejections}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
