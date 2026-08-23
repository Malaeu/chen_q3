#!/usr/bin/env python3
"""Q3 typed I/O port matcher — T2.2 fail-closed release.

Schema of authority: docs/cartographer/typed_io_schema_v1_2.yaml.
Fixtures: docs/cartographer/comparator/fixtures/*.json (kernel exact_type
strings pasted from `lake env lean` #check output — never reconstructed).

This module belongs to the Q3_TDC (Q3 Typed Discovery Compiler) layer of
Q3_MathOS; the ports it classifies name Q3_MSL entries.

THE FAIL-CLOSED LAW (the repair that T2.1 failed):

    absence of metadata or evidence never upgrades to a proof edge.

Concretely, versus T2.1:
  * every port is validated against REQUIRED_PORT_FIELDS before matching;
    a missing field returns UNVERIFIED, never EXACT_MATCH;
  * trust has NO permissive default -- `provider.get("trust", "LEAN")` is
    gone; an undeclared trust or trust_floor is UNVERIFIED;
  * every adapter is validated (required fields, EVIDENCE completeness,
    verifier, direction, scope, loss ledger, shared context, and the
    declared REQUIRED_INPUT) before it may license an edge; a registry row
    that merely carries the right two strings is rejected;
  * representative transitions are a declared table, not a linear order:
    WEAKENING is free, CONSTRUCTION needs an adapter carrying the required
    witness (an a.e. function is NOT an Lp element without MemLp),
    FORBIDDEN is REFINEMENT_LOSS, and anything undeclared is UNVERIFIED.

Retained from T2.1: hard gates before ranking, the scope preorder, the
declared-adaptable-pair vs undeclared-identity distinction, hyperedge
context coherence, and the closed result enum.

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
SCOPE_ORDER = {"FINITE_CELL": 0, "COFINAL_FAMILY": 1, "ABSTRACT": 1}

REQUIRED_PORT_FIELDS = {
    "provider": ("kernel_type", "source_family", "trust"),
    "consumer": ("kernel_type", "source_family", "trust_floor"),
}
ACCEPTED_TRUST = ("LEAN", "ARB_INTERVAL")
VALID_TRUST = ("LEAN", "ARB_INTERVAL", "PAPER", "CONDITIONAL")

REQUIRED_ADAPTER_FIELDS = ("ADAPTER_ID", "FROM_PORT", "TO_PORT", "EVIDENCE",
                           "DIRECTION", "PRESERVES", "DROPS", "LOSS_LEDGER",
                           "SCOPE", "VERIFIER", "SHARED_PARAMETER_CONTEXT",
                           "COST")
REQUIRED_EVIDENCE_FIELDS = ("theorem_name", "source_file", "source_line",
                            "source_commit", "source_blob", "check_type")
VALID_DIRECTIONS = ("forward", "both")

# Declared representative transition table (schema v1.2).  An entry absent
# from this table is UNVERIFIED, not a silent pass.
REPRESENTATIVE_TRANSITIONS = {
    ("pointwise", "ae-representative"): {"kind": "WEAKENING"},
    ("ae-representative", "pointwise"): {"kind": "FORBIDDEN"},
    ("full-endpoint-production", "midpoint-pointwise"): {"kind": "FORBIDDEN"},
    ("ae-representative", "Lp-class"): {"kind": "CONSTRUCTION",
                                        "required_input": "MemLp"},
    ("MemLp-witness", "Lp-class"): {"kind": "CONSTRUCTION",
                                    "required_input": "MemLp"},
    ("Lp-class", "ae-representative"): {"kind": "WEAKENING"},
}

HERE = os.path.dirname(os.path.abspath(__file__))
FIXTURES = os.path.join(HERE, "fixtures")
CARTOGRAPHER = os.path.dirname(HERE)
REPO_ROOT = os.path.dirname(os.path.dirname(CARTOGRAPHER))


def _load(name: str):
    with open(os.path.join(FIXTURES, name), encoding="utf-8") as fh:
        return json.load(fh)


def load_registry():
    """Adapter registry with evidence-bearing records."""
    return _load("adapter_registry.json")


def load_adaptable_pairs():
    return {tuple(p) for p in _load("adaptable_pairs.json")}


# --------------------------------------------------------------------------
# validation layer (new in T2.2) — runs before any matching
# --------------------------------------------------------------------------

def validate_port(port: dict, role: str):
    """Return None if the port can be classified, else a reason string.

    Fail-closed: an absent required field is not a wildcard.
    """
    if not isinstance(port, dict):
        return f"{role} port is not a record"
    for field in REQUIRED_PORT_FIELDS[role]:
        if port.get(field) in (None, ""):
            return f"{role} port is missing required field '{field}'"
    trust_field = "trust" if role == "provider" else "trust_floor"
    if port[trust_field] not in VALID_TRUST:
        return (f"{role} port declares unknown {trust_field} "
                f"'{port[trust_field]}'")
    return None


def validate_adapter(adapter: dict):
    """Return None if the adapter record is evidence-bearing, else a reason.

    T2.1 accepted any row whose FROM_PORT/TO_PORT strings lined up.  A
    registry is data, not an axiom table: every field is checked here.
    """
    if not isinstance(adapter, dict):
        return "adapter record is not a record"
    aid = adapter.get("ADAPTER_ID", "<unnamed>")
    for field in REQUIRED_ADAPTER_FIELDS:
        if field not in adapter or adapter[field] in (None, ""):
            return f"adapter {aid} is missing required field '{field}'"
    evidence = adapter["EVIDENCE"]
    if not isinstance(evidence, dict):
        return f"adapter {aid} EVIDENCE is not a record"
    for field in REQUIRED_EVIDENCE_FIELDS:
        if evidence.get(field) in (None, ""):
            return f"adapter {aid} EVIDENCE is missing '{field}'"
    if adapter["VERIFIER"] not in ACCEPTED_TRUST:
        return (f"adapter {aid} verifier {adapter['VERIFIER']} is below the "
                "proof-edge floor")
    if adapter["DIRECTION"] not in VALID_DIRECTIONS:
        return f"adapter {aid} declares unknown DIRECTION"
    if adapter["SCOPE"] not in SCOPE_ORDER:
        return f"adapter {aid} declares unknown SCOPE"
    if not isinstance(adapter["PRESERVES"], list) or \
       not isinstance(adapter["DROPS"], list):
        return f"adapter {aid} PRESERVES/DROPS are not lists"
    if not isinstance(adapter["SHARED_PARAMETER_CONTEXT"], dict):
        return f"adapter {aid} SHARED_PARAMETER_CONTEXT is not a map"
    return None


def _find_adapter(registry, key, have, want, provider=None):
    """Find a VALIDATED adapter for have -> want on `key`.

    Returns (adapter, reason).  Exactly one of the two is None.  A malformed
    candidate is reported rather than skipped, so a fabricated row cannot be
    silently replaced by a later lawful one.
    """
    for a in registry:
        if not isinstance(a, dict):
            continue
        if a.get("FROM_PORT", {}).get(key) != have or \
           a.get("TO_PORT", {}).get(key) != want:
            continue
        reason = validate_adapter(a)
        if reason:
            return None, reason
        required = a.get("REQUIRED_INPUT")
        if required:
            carried = (provider or {}).get("construction_witness")
            if carried != required:
                return None, (f"adapter {a['ADAPTER_ID']} requires the "
                              f"construction witness '{required}'; provider "
                              f"carries {carried!r}")
        return a, None
    return None, None


# --------------------------------------------------------------------------
# matching
# --------------------------------------------------------------------------

def _match_representative(provider, consumer, registry, chain, trace):
    """Classify the representative transition.  Returns None to continue, or
    a terminal (result, reasons, chain) triple."""
    pv, cv = provider.get("representative"), consumer.get("representative")
    if pv is None or cv is None or pv == cv:
        return None
    rule = REPRESENTATIVE_TRANSITIONS.get((pv, cv))
    if rule is None:
        return ("UNVERIFIED",
                [f"representative transition {pv} -> {cv} is not declared in "
                 "the schema transition table"], None)
    if rule["kind"] == "FORBIDDEN":
        return ("REFINEMENT_LOSS",
                [f"representative {pv} cannot discharge a {cv} consumer "
                 "(C04/C10: a.e. never discharges pointwise)"], None)
    if rule["kind"] == "WEAKENING":
        adapter, reason = _find_adapter(registry, "representative", pv, cv,
                                        provider)
        if reason:
            return "UNVERIFIED", [reason], None
        if adapter:
            chain.append(adapter["ADAPTER_ID"])
            trace.append(f"adapter {adapter['ADAPTER_ID']} "
                         f"({adapter['VERIFIER']})")
        else:
            trace.append(f"representative weakening {pv} -> {cv} (lawful)")
        return None
    # CONSTRUCTION
    adapter, reason = _find_adapter(registry, "representative", pv, cv,
                                    provider)
    if reason:
        return "UNVERIFIED", [reason], None
    if adapter is None:
        return ("ADAPTER_REQUIRED",
                [f"representative {pv} -> {cv} is a CONSTRUCTION requiring "
                 f"{rule['required_input']}; no validated adapter registered"],
                None)
    chain.append(adapter["ADAPTER_ID"])
    trace.append(f"construction {adapter['ADAPTER_ID']} "
                 f"({adapter['EVIDENCE']['theorem_name']})")
    return None


def match_port(provider: dict, consumer: dict, registry, adaptable_pairs,
               trace: Optional[list] = None):
    """Classify one provider->consumer edge.  Returns (result, reasons, chain)."""
    if trace is None:
        trace = []
    chain: list = []

    # 0) schema validation — fail closed before anything else
    for port, role in ((provider, "provider"), (consumer, "consumer")):
        reason = validate_port(port, role)
        if reason:
            return "UNVERIFIED", [reason], None

    # 1) trust floor (no permissive default: both sides are declared by now)
    if provider["trust"] not in ACCEPTED_TRUST and \
       consumer["trust_floor"] == "LEAN":
        return "HARD_MISMATCH", ["trust below task floor"], None

    # 2) scope preorder
    pv, cv = provider.get("scope"), consumer.get("scope")
    if pv is not None and cv is not None and \
       SCOPE_ORDER.get(pv, 0) < SCOPE_ORDER.get(cv, 1):
        return "HARD_MISMATCH", [f"scope {pv} offered to {cv} consumer"], None

    # 3) hard gates
    for k in HARD_GATE_KEYS:
        pv, cv = provider.get(k), consumer.get(k)
        if pv is None or cv is None or pv == cv:
            continue
        if k == "object_identity":
            adapter, reason = _find_adapter(registry, k, pv, cv, provider)
            if reason:
                return "UNVERIFIED", [reason], None
            if adapter:
                chain.append(adapter["ADAPTER_ID"])
                trace.append(f"adapter {adapter['ADAPTER_ID']} "
                             f"({adapter['VERIFIER']})")
                continue
            if (pv, cv) in adaptable_pairs:
                return "ADAPTER_REQUIRED", [
                    f"declared adaptable pair ({pv} -> {cv}) has no verified "
                    "adapter registered"], None
            return "HARD_MISMATCH", [
                f"object {pv} is not the consumer object {cv}; pair "
                "undeclared; no verified adapter"], None
        return "HARD_MISMATCH", [f"{k}: provider={pv} consumer={cv}"], None

    # 4) representative transition table
    terminal = _match_representative(provider, consumer, registry, chain, trace)
    if terminal is not None:
        return terminal

    # 5) remaining soft refinements
    for k in ("carrier", "summation_method", "topology"):
        pv, cv = provider.get(k), consumer.get(k)
        if pv is None or cv is None or pv == cv:
            continue
        adapter, reason = _find_adapter(registry, k, pv, cv, provider)
        if reason:
            return "UNVERIFIED", [reason], None
        if adapter:
            chain.append(adapter["ADAPTER_ID"])
            trace.append(f"adapter {adapter['ADAPTER_ID']}")
        elif consumer.get(k + "_strict"):
            return "REFINEMENT_LOSS", [f"{k}: {pv} vs required {cv}"], None
        else:
            return "ADAPTER_REQUIRED", [f"{k}: {pv} vs {cv}; no adapter"], None

    # 6) verdict
    if chain:
        return "EXPLICIT_ADAPTER_MATCH", trace, chain
    if provider["kernel_type"] == consumer["kernel_type"]:
        return "EXACT_MATCH", trace, []
    return "ADAPTER_REQUIRED", ["kernel types differ; no adapter chain"], None


def match_hyperedge(providers: list, consumer_ports: list, registry,
                    adaptable_pairs):
    """Match an AND-hyperedge under ONE substitution environment.

    Every consumer port lists CONTEXT vars; every provider binds them.  All
    bindings must agree across the edge; otherwise HARD_MISMATCH
    (SHARED_CONTEXT_INCOHERENCE) — even if every pairwise surface matches.
    Port validation runs first, so an unvalidatable port fails the edge
    closed.
    """
    if len(providers) != len(consumer_ports):
        return "HARD_MISMATCH", ["arity mismatch"], None
    for p in providers:
        reason = validate_port(p, "provider")
        if reason:
            return "UNVERIFIED", [reason], None
    for c in consumer_ports:
        reason = validate_port(c, "consumer")
        if reason:
            return "UNVERIFIED", [reason], None
    env: dict = {}
    for p, c in zip(providers, consumer_ports):
        for var, _cval in c.get("context", {}).items():
            pval = p.get("context", {}).get(var)
            if pval is None:
                return "HARD_MISMATCH", [
                    f"provider does not bind shared var {var}"], None
            if var in env and env[var] != pval:
                return "HARD_MISMATCH", [
                    "SHARED_CONTEXT_INCOHERENCE: var "
                    f"{var} bound to {env[var]} and {pval} across the edge"], None
            env[var] = pval
    chains = []
    for p, c in zip(providers, consumer_ports):
        res, why, chain = match_port(p, c, registry, adaptable_pairs)
        if res in ("HARD_MISMATCH", "REFINEMENT_LOSS", "ADAPTER_REQUIRED",
                   "UNVERIFIED"):
            return res, why, None
        chains.append(chain)
    return "EXPLICIT_ADAPTER_MATCH" if any(chains) else "EXACT_MATCH", \
        [f"env={env}"], chains


# --------------------------------------------------------------------------
# receipt
# --------------------------------------------------------------------------

def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        h.update(fh.read())
    return h.hexdigest()


def toolchain() -> dict:
    """Pinned kernel identity, read from disk — never recalled from memory."""
    lean_toolchain_path = os.path.join(REPO_ROOT, "q3.lean.aristotle",
                                       "lean-toolchain")
    manifest_path = os.path.join(REPO_ROOT, "q3.lean.aristotle",
                                 "lake-manifest.json")
    with open(lean_toolchain_path, encoding="utf-8") as fh:
        lean = fh.read().strip()
    mathlib_rev = None
    with open(manifest_path, encoding="utf-8") as fh:
        manifest = json.load(fh)
    for pkg in manifest.get("packages", []):
        if pkg.get("name") == "mathlib":
            mathlib_rev = pkg.get("rev")
    return {"lean_toolchain": lean, "mathlib_rev": mathlib_rev}


def receipt(results: Optional[dict] = None) -> dict:
    """Content-addressed T2_PORT_MATCHER_RECEIPT_V1 — now schema-complete.

    `toolchain` and `results` are mandatory in RECEIPT_V1; T2.1 shipped
    without them and was killed for it.  `results` is filled by the replay
    suite, which passes its frozen plant outcomes in.
    """
    files = {
        "schema": os.path.join(CARTOGRAPHER, "typed_io_schema_v1_2.yaml"),
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
        "toolchain": toolchain(),
        "results": results if results is not None else {},
        "replay_command":
            "python3 docs/cartographer/comparator/test_port_matcher.py",
    }


if __name__ == "__main__":
    print(json.dumps(receipt(), indent=2, ensure_ascii=False))
