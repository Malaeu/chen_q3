"""Plants for the Control-v9 external semantic-attestation broker.

The broker is the only durable source of attestations, so its refusals matter
as much as its answers: a lookup must never become a path, and a stored object
that drifts from the closed schema must not resolve.
"""

from __future__ import annotations

import json
import tempfile
import threading
import time
import unittest
from pathlib import Path

from orchestrator import semantic_attestation_broker as broker
from orchestrator import three_body_loop

RECEIPT = {
    "schema": "q3_semantic_attestation.v1",
    "attestation_id": "ATTEST_BROKER_PLANT_V1",
    "issuer": "LINUX_INDEPENDENT_SEMANTIC_AUDITOR",
    "status": "ADMITTED",
    "control_version": 9,
    "task_path": "docs/Codex/TASK.md",
    "task_blob": "0" * 40,
    "source_commit": "1" * 40,
    "source_git_blob": "2" * 40,
    "theorem_ids": ["Q3.Plant.theorem"],
    "admitted_scope": ["production"],
    "terminal_consumer": "plant",
    "closes": ["PLANT_CLOSES"],
    "opens": ["PLANT_OPENS"],
    "normalization": "plant normalization",
    "domain": "plant domain",
    "quantifiers": "plant quantifiers",
    "hypothesis_provenance_sha256": "3" * 64,
}


class BrokerPlants(unittest.TestCase):
    def _registry(self, root: Path, receipt: dict | None = RECEIPT) -> Path:
        registry = root / "receipts"
        registry.mkdir(parents=True, exist_ok=True)
        if receipt is not None:
            (registry / f"{receipt['attestation_id']}.json").write_text(json.dumps(receipt))
        return registry

    def test_lookup_returns_the_exact_stored_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            registry = self._registry(Path(tmp))
            found = broker.lookup(RECEIPT["attestation_id"], registry_dir=registry)
            self.assertEqual(found, RECEIPT)

    def test_PLANT_lookup_is_not_a_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            registry = self._registry(Path(tmp))
            outside = Path(tmp) / "secret.json"
            outside.write_text(json.dumps(RECEIPT))
            for hostile in (
                "../secret",
                "/etc/passwd",
                "..\\secret",
                ".hidden",
                "a/b",
                "",
                "x" * 300,
            ):
                self.assertIsNone(broker.lookup(hostile, registry_dir=registry))

    def test_PLANT_issuer_drift_does_not_resolve(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            forged = dict(RECEIPT, issuer="CODEX_EXECUTOR")
            registry = self._registry(Path(tmp), forged)
            self.assertIsNone(broker.lookup(forged["attestation_id"], registry_dir=registry))

    def test_PLANT_id_mismatch_does_not_resolve(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            mismatched = dict(RECEIPT, attestation_id="ATTEST_OTHER")
            registry = Path(tmp) / "receipts"
            registry.mkdir(parents=True)
            (registry / f"{RECEIPT['attestation_id']}.json").write_text(json.dumps(mismatched))
            self.assertIsNone(
                broker.lookup(RECEIPT["attestation_id"], registry_dir=registry)
            )

    def test_PLANT_unknown_id_resolves_to_none(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            registry = self._registry(Path(tmp))
            self.assertIsNone(broker.lookup("ATTEST_NEVER_ISSUED", registry_dir=registry))

    def test_client_and_broker_agree_over_the_socket(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            registry = self._registry(root)
            socket_path = root / "attestation.sock"
            original = broker.REGISTRY_DIR
            broker.REGISTRY_DIR = registry
            server = broker._Server(str(socket_path), broker._Handler)
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            try:
                for _ in range(50):
                    if socket_path.exists():
                        break
                    time.sleep(0.02)
                resolved = three_body_loop.resolve_linux_semantic_attestation(
                    RECEIPT["attestation_id"], socket_path=socket_path
                )
                self.assertEqual(resolved, RECEIPT)
                missing = three_body_loop.resolve_linux_semantic_attestation(
                    "ATTEST_NEVER_ISSUED", socket_path=socket_path
                )
                self.assertIsNone(missing)
            finally:
                server.shutdown()
                server.server_close()
                broker.REGISTRY_DIR = original

    def test_PLANT_unavailable_broker_resolves_to_none(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            dead = Path(tmp) / "not-listening.sock"
            self.assertIsNone(
                three_body_loop.resolve_linux_semantic_attestation(
                    RECEIPT["attestation_id"], socket_path=dead
                )
            )


if __name__ == "__main__":
    unittest.main()
