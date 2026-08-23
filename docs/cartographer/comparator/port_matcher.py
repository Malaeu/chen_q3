#!/usr/bin/env python3
"""Q3 typed I/O port matcher — durable T2.1 release.

Schema of authority: docs/cartographer/typed_io_schema_v1_1.yaml.
Fixtures: docs/cartographer/comparator/fixtures/*.json (kernel exact_type
strings pasted from `lake env lean` #check output — never reconstructed).

Laws implemented:
  * hard gates before any ranking (trust floor, source_family, scope
    preorder FINITE_CELL < {COFINAL_FAMILY, ABSTRACT}, quantifier spine,
    normalization, units, object identity);
  * declared ADAPTABLE_PAIRS without a registered adapter -> ADAPTER_REQUIRED;
    undeclared identity pair -> HARD_MISMATCH;
  * representative semantics: pointwise > ae-representative > Lp-class; an
    a.e./Lp provider never discharges a pointwise consumer (C04/C10);
  * hyperedge context coherence: ONE substitution environment for the whole
    AND-edge; inconsistent bindings -> HARD_MISMATCH
    (SHARED_CONTEXT_INCOHERENCE), regardless of per-port surface matches;
  * closed result enum PORT_MATCH_RESULT_V1.

No live-route mutation: this module reads fixtures and classifies; it never
writes to the repository.
"""

from __future__ import annotations

import hashlib
import json
import os
from typing import Optional

RESULTS = ("EXACT_MATCH", "DEFINITIONAL_MATCH", "EXPLICIT_ADAPTER_MATCH",
           "ADAPTER_REQUIRED", "REFINEMENT_LOSS", "HARD_MISMATCH", "UNVERIFIED")

HARD_GATE_KEYS = ("source_family", "quantifier_spine", "normalization",
                  "units", "object_identity")
SOFT_KEYS = ("carrier", "representative", "summation_method", "topology")
SCOPE_ORDER = {"FINITE_CELL": 0, "COFINAL_FAMILY": 1, "ABSTRACT": 1}
REPR_ORDER = {"pointwise": 2, "ae-representative": 1, "Lp-class": 0}

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURES = os.path.join(HERE, "fixtures")


def _load(name: str):
    with open(os.path.join(FIXTURES, name), encoding="utf-8") as fh:
        return json.load(fh)


def load_registry():
    """Adapter registry with evidence-bearing records (T2.1)."""
    return _load("adapter_registry.json")


def load_adaptable_pairs():
    return {tuple(p) for p in _load("adaptable_pairs.json")}


def _find_adapter(registry, key, have, want):
    for a in registry:
        if a["FROM_PORT"].get(key) == have and a["TO_PORT"].get(key) == want:
            return a
    return None


def _representative_ok(pv: str, cv: str) -> bool:
    """Strong provider representative may feed a weak consumer; never the
    reverse (the a.e./pointwise firewall)."""
    return REPR_ORDER.get(pv, 0) >= REPR_ORDER.get(cv, 0)


def match_port(provider: dict, consumer: dict, registry, adaptable_pairs,
               trace: Optional[list] = None):
    """Classify one provider->consumer edge.  Returns (result, reasons, chain)."""
    if trace is None:
        trace = []
    chain: list = []

    # 0) trust floor
    if provider.get("trust", "LEAN") not in ("LEAN", "ARB_INTERVAL") and \
       consumer.get("trust_floor", "LEAN") == "LEAN":
        return "HARD_MISMATCH", ["trust below task floor"], None

    # 1) scope preorder
    pv, cv = provider.get("scope"), consumer.get("scope")
    if pv is not None and cv is not None and \
       SCOPE_ORDER.get(pv, 0) < SCOPE_ORDER.get(cv, 1):
        return "HARD_MISMATCH", [f"scope {pv} offered to {cv} consumer"], None

    # 2) hard gates
    for k in HARD_GATE_KEYS:
        pv, cv = provider.get(k), consumer.get(k)
        if pv is None or cv is None or pv == cv:
            continue
        if k == "object_identity":
            a = _find_adapter(registry, k, pv, cv)
            if a:
                chain.append(a["ADAPTER_ID"])
                trace.append(f"adapter {a['ADAPTER_ID']} ({a['VERIFIER']})")
                continue
            if (pv, cv) in adaptable_pairs:
                return "ADAPTER_REQUIRED", [
                    f"declared adaptable pair ({pv} -> {cv}) has no verified "
                    "adapter registered"], None
            return "HARD_MISMATCH", [
                f"object {pv} is not the consumer object {cv}; pair "
                "undeclared; no verified adapter"], None
        return "HARD_MISMATCH", [f"{k}: provider={pv} consumer={cv}"], None

    # 3) representative firewall (checked before generic soft keys)
    pv, cv = provider.get("representative"), consumer.get("representative")
    if pv is not None and cv is not None and pv != cv:
        if pv in REPR_ORDER and cv in REPR_ORDER:
            if not _representative_ok(pv, cv):
                # weak representative offered to a stronger consumer: an
                # adapter can never fix this without a new pointwise theorem
                return ("REFINEMENT_LOSS",
                        [f"representative {pv} cannot discharge {cv} consumer "
                         "(a.e./Lp never discharges pointwise; C04/C10)"], None)
            trace.append(f"representative weakening {pv} -> {cv} (lawful)")
        else:
            a = _find_adapter(registry, "representative", pv, cv)
            if a:
                chain.append(a["ADAPTER_ID"])
            elif consumer.get("representative_strict"):
                return "REFINEMENT_LOSS", [
                    f"representative: {pv} vs required {cv}"], None
            else:
                return "ADAPTER_REQUIRED", [
                    f"representative: {pv} vs {cv}; no adapter"], None

    # 4) remaining soft refinements
    for k in ("carrier", "summation_method", "topology"):
        pv, cv = provider.get(k), consumer.get(k)
        if pv is None or cv is None or pv == cv:
            continue
        a = _find_adapter(registry, k, pv, cv)
        if a:
            chain.append(a["ADAPTER_ID"])
            trace.append(f"adapter {a['ADAPTER_ID']}")
        elif consumer.get(k + "_strict"):
            return "REFINEMENT_LOSS", [f"{k}: {pv} vs required {cv}"], None
        else:
            return "ADAPTER_REQUIRED", [f"{k}: {pv} vs {cv}; no adapter"], None

    # 5) verdict
    if chain:
        return "EXPLICIT_ADAPTER_MATCH", trace, chain
    if provider["kernel_type"] == consumer["kernel_type"]:
        return "EXACT_MATCH", trace, []
    return "ADAPTER_REQUIRED", ["kernel types differ; no adapter chain"], None


def match_hyperedge(providers: list, consumer_ports: list, registry,
                    adaptable_pairs):
    """Match an AND-hyperedge under ONE substitution environment.

    Every consumer port lists CONTEXT vars (e.g. {"m": "m", "N": "N"}).
    Every provider binds them (e.g. {"m": "m1", "N": "N1"}).  All bindings
    must agree across the edge; otherwise HARD_MISMATCH
    (SHARED_CONTEXT_INCOHERENCE) — even if every pairwise surface matches.
    """
    if len(providers) != len(consumer_ports):
        return "HARD_MISMATCH", ["arity mismatch"], None
    env: dict = {}
    for p, c in zip(providers, consumer_ports):
        for var, cval in c.get("context", {}).items():
            pval = p.get("context", {}).get(var)
            if pval is None:
                return "HARD_MISMATCH", [
                    f"provider does not bind shared var {var}"], None
            if var in env and env[var] != pval:
                return "HARD_MISMATCH", [
                    "SHARED_CONTEXT_INCOHERENCE: var "
                    f"{var} bound to {env[var]} and {pval} across the edge"], None
            env[var] = pval
    # coherent context: now match ports pairwise
    chains = []
    for p, c in zip(providers, consumer_ports):
        res, why, chain = match_port(p, c, registry, adaptable_pairs)
        if res in ("HARD_MISMATCH", "REFINEMENT_LOSS", "ADAPTER_REQUIRED",
                   "UNVERIFIED"):
            return res, why, None
        chains.append(chain)
    return "EXPLICIT_ADAPTER_MATCH" if any(chains) else "EXACT_MATCH", \
        [f"env={env}"], chains


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        h.update(fh.read())
    return h.hexdigest()


def receipt() -> dict:
    """Content-addressed T2_PORT_MATCHER_RECEIPT_V1."""
    root = os.path.dirname(HERE)          # docs/cartographer
    files = {
        "schema": os.path.join(root, "typed_io_schema_v1_1.yaml"),
        "matcher": os.path.join(HERE, "port_matcher.py"),
        "tests": os.path.join(HERE, "test_port_matcher.py"),
    }
    fixture_manifest = {}
    for name in sorted(os.listdir(FIXTURES)):
        fixture_manifest[name] = sha256_file(os.path.join(FIXTURES, name))
    return {
        "RECEIPT": "T2_PORT_MATCHER_RECEIPT_V1",
        "schema_sha256": sha256_file(files["schema"]),
        "matcher_sha256": sha256_file(files["matcher"]),
        "tests_sha256": sha256_file(files["tests"]),
        "fixture_manifest": fixture_manifest,
        "replay_command":
            "python3 docs/cartographer/comparator/test_port_matcher.py",
    }


if __name__ == "__main__":
    print(json.dumps(receipt(), indent=2, ensure_ascii=False))
