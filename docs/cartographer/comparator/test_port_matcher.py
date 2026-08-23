#!/usr/bin/env python3
"""T2.2 fail-closed replay suite: P1-P10, NC1/NC2/NC4/NC5, C2 (+ coherent
control).

PASS criteria (verdict 7a92845e):
  every expected outcome preserved; wrong-object escape = 0; false rejection
  = 0; the emitted receipt carries schema/matcher/tests/fixtures/toolchain
  and the frozen plant results.  The receipt is printed, never written
  beside the sources: a receipt file inside the hashed tree would hash
  itself and stop being reproducible.

Registry selectors used by the fixtures:
  "current"       the shipped evidence-bearing registry;
  "pre_w1"        the registry as it stood before the W1 crosswalk landed;
  "fake_adapter"  a single fabricated row carrying the right two strings and
                  no EVIDENCE — P9's attack on the T2.1 axiom-table bug.
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import port_matcher as pm  # noqa: E402

FAKE_REGISTRY = [{
    "ADAPTER_ID": "A_FABRICATED",
    "FROM_PORT": {"object_identity": "A"},
    "TO_PORT": {"object_identity": "B"},
    "DIRECTION": "forward",
    "VERIFIER": "LEAN",
}]

ACCEPTING = ("EXACT_MATCH", "DEFINITIONAL_MATCH", "EXPLICIT_ADAPTER_MATCH")


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
    results = {}
    for pid, plant in plants.items():
        if pid.startswith("_"):
            continue
        selector = plant.get("registry")
        if selector == "pre_w1":
            reg = pre_w1
        elif selector == "fake_adapter":
            reg = FAKE_REGISTRY
        else:
            reg = registry
        if "providers" in plant:
            got, why, _chain = pm.match_hyperedge(
                plant["providers"], plant["consumer_ports"], reg, pairs)
        else:
            got, why, _chain = pm.match_port(
                plant["provider"], plant["consumer"], reg, pairs)
        exp = plant["expected"]
        ok = got == exp
        results[pid] = {"expected": exp, "got": got,
                        "status": "PASS" if ok else "FAIL"}
        print(f"{pid:7s} {plant['name'][:52]:52s} expected={exp:24s} "
              f"got={got:24s} {'PASS' if ok else 'FAIL'}")
        if not ok:
            failures += 1
            print(f"        why: {why}")
            if exp not in ACCEPTING and got in ACCEPTING:
                wrong_object_escapes += 1
            if exp in ACCEPTING and got not in ACCEPTING:
                false_rejections += 1
    print(f"FAILURES={failures} WRONG_OBJECT_ESCAPE={wrong_object_escapes} "
          f"FALSE_REJECTION={false_rejections}")

    receipt = pm.receipt(results)
    missing = [f for f in ("schema_sha256", "matcher_sha256", "tests_sha256",
                           "fixture_manifest", "toolchain", "results",
                           "replay_command") if not receipt.get(f)]
    if missing:
        print(f"RECEIPT INCOMPLETE: missing {missing}")
        return 1
    print("RECEIPT COMPLETE (all mandatory fields present)")
    print(json.dumps(receipt, indent=2, ensure_ascii=False))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
