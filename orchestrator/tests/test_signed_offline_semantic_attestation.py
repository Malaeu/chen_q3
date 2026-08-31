"""Plants for the Control-v9 Darwin signed-offline attestation transport."""

from __future__ import annotations

import hashlib
import inspect
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from orchestrator import three_body_loop as loop


ATTESTATION_ID = "ATTEST_SIGNED_OFFLINE_PLANT_V1"
RECEIPT = {
    "schema": "q3_semantic_attestation.v1",
    "attestation_id": ATTESTATION_ID,
    "issuer": "LINUX_INDEPENDENT_SEMANTIC_AUDITOR",
    "status": "ADMITTED",
    "control_version": 9,
    "task_path": "docs/Codex/TASK.md",
    "task_blob": "0" * 40,
    "source_commit": "1" * 40,
    "source_git_blob": "2" * 40,
    "theorem_ids": ["Q3.Plant.theorem"],
    "admitted_scope": ["PLANT_SCOPE"],
    "terminal_consumer": "plant consumer",
    "closes": ["PLANT_CLOSES"],
    "opens": [],
    "normalization": "plant normalization",
    "domain": "plant domain",
    "quantifiers": "plant quantifiers",
    "hypothesis_provenance_sha256": hashlib.sha256(b"[]").hexdigest(),
}


class SignedOfflinePlants(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.bundle = self.root / "bundle"
        self.trust = self.root / "trust"
        self.bundle.mkdir(mode=0o700)
        self.trust.mkdir(mode=0o700)
        self.key = self.root / "auditor"
        subprocess.run(
            ["/usr/bin/ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", str(self.key)],
            check=True,
        )
        self.allowed = self.trust / "allowed_signers"
        self.revocations = self.trust / "revocations.json"
        self.tracked_revocations = self.bundle / "semantic_attestation_revoked_ids.v1.json"
        self._write_allowed_signers(self.key)
        self._write_revocations([])
        self._write_tracked_revocations([])
        self.patchers = [
            mock.patch.object(loop, "REPO_ROOT", self.root),
            mock.patch.object(loop, "SIGNED_OFFLINE_BUNDLE_DIR", self.bundle),
            mock.patch.object(loop, "SIGNED_OFFLINE_ALLOWED_SIGNERS", self.allowed),
            mock.patch.object(loop, "SIGNED_OFFLINE_REVOCATIONS", self.revocations),
            mock.patch.object(loop, "SIGNED_OFFLINE_TRUST_OWNER_UID", os.getuid()),
        ]
        for patcher in self.patchers:
            patcher.start()

    def tearDown(self) -> None:
        for patcher in reversed(self.patchers):
            patcher.stop()
        self.tmp.cleanup()

    def assert_code(self, code: str, fn, *args, **kwargs) -> loop.ThreeBodyViolation:
        with self.assertRaises(loop.ThreeBodyViolation) as caught:
            fn(*args, **kwargs)
        self.assertEqual(caught.exception.code, code)
        return caught.exception

    def _paths(self, attestation_id: str = ATTESTATION_ID) -> tuple[Path, Path]:
        receipt = self.bundle / f"{attestation_id}.receipt.json"
        signature = self.bundle / f"{attestation_id}.receipt.sshsig"
        return receipt, signature

    def _write_allowed_signers(
        self,
        key: Path,
        *,
        principal: str = loop.SIGNED_OFFLINE_PRINCIPAL,
        namespace: str = loop.SIGNED_OFFLINE_NAMESPACE,
    ) -> None:
        public = key.with_suffix(".pub").read_text(encoding="ascii").strip()
        self.allowed.write_text(
            f'{principal} namespaces="{namespace}" {public}\n', encoding="ascii"
        )
        self.allowed.chmod(0o600)

    def _write_revocations(self, revoked: list[str]) -> None:
        self.revocations.write_text(
            json.dumps(
                {
                    "schema": "q3_semantic_attestation_revocations.v1",
                    "revoked_attestation_ids": revoked,
                },
                sort_keys=True,
                separators=(",", ":"),
            )
            + "\n",
            encoding="utf-8",
        )
        self.revocations.chmod(0o600)

    def _write_tracked_revocations(self, revoked: list[str]) -> None:
        payload = {
            "schema": "q3_semantic_attestation_revocations.v1",
            "revoked_attestation_ids": revoked,
        }
        self.tracked_revocations.write_bytes(loop._canonical_json_bytes(payload) + b"\n")

    def _write_bundle(
        self,
        receipt: dict = RECEIPT,
        *,
        key: Path | None = None,
        namespace: str = loop.SIGNED_OFFLINE_NAMESPACE,
    ) -> tuple[Path, Path]:
        receipt_path, signature_path = self._paths(receipt["attestation_id"])
        receipt_path.write_bytes(loop._canonical_json_bytes(receipt) + b"\n")
        subprocess.run(
            [
                "/usr/bin/ssh-keygen",
                "-Y",
                "sign",
                "-f",
                str(key or self.key),
                "-n",
                namespace,
                str(receipt_path),
            ],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        receipt_path.with_name(receipt_path.name + ".sig").replace(signature_path)
        return receipt_path, signature_path

    @staticmethod
    def _entry(receipt: dict, *, entry_id: str = "ENTRY_SIGNED_OFFLINE_PLANT") -> dict:
        return {
            "entry_id": entry_id,
            "status": "SEMANTICALLY_ADMITTED",
            "task_path": receipt["task_path"],
            "task_blob": receipt["task_blob"],
            "source_path": "Q3/Plant.lean",
            "source_commit": receipt["source_commit"],
            "source_git_blob": receipt["source_git_blob"],
            "theorem_ids": receipt["theorem_ids"],
            "admitted_scope": receipt["admitted_scope"],
            "terminal_consumer": receipt["terminal_consumer"],
            "closes": receipt["closes"],
            "opens": receipt["opens"],
            "normalization": receipt["normalization"],
            "domain": receipt["domain"],
            "quantifiers": receipt["quantifiers"],
            "hypothesis_provenance": [],
            "hypothesis_provenance_sha256": receipt["hypothesis_provenance_sha256"],
            "semantic_attestation_id": receipt["attestation_id"],
        }

    def test_valid_bundle_passes_with_socket_and_network_absent(self) -> None:
        self._write_bundle()
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.object(
            loop, "resolve_linux_semantic_attestation", side_effect=AssertionError("network")
        ):
            self.assertEqual(loop.resolve_semantic_attestation(ATTESTATION_ID), RECEIPT)

    def test_explicit_mac_tracked_receipt_fallback_recovers_missing_signature(self) -> None:
        receipt, _ = self._paths()
        receipt.write_bytes(loop._canonical_json_bytes(RECEIPT) + b"\n")
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ):
            self.assertEqual(loop.resolve_semantic_attestation(ATTESTATION_ID), RECEIPT)

    def test_exact_owner_waiver_uses_only_the_tracked_receipt(self) -> None:
        with mock.patch.object(
            loop,
            "resolve_tracked_semantic_attestation",
            return_value=RECEIPT,
        ) as tracked, mock.patch.object(
            loop,
            "resolve_signed_offline_semantic_attestation",
            side_effect=AssertionError("owner waiver entered signed transport"),
        ):
            for _entry_id, attestation_id in sorted(loop.EXACT_OWNER_WAIVERS):
                with self.subTest(attestation_id=attestation_id):
                    self.assertEqual(
                        loop.resolve_semantic_attestation(attestation_id),
                        RECEIPT,
                    )
        self.assertEqual(
            tracked.call_args_list,
            [mock.call(attestation_id) for _, attestation_id in sorted(loop.EXACT_OWNER_WAIVERS)],
        )

    def test_signed_path_stays_primary_when_fallback_is_enabled(self) -> None:
        self._write_bundle()
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ), mock.patch.object(
            loop,
            "resolve_tracked_semantic_attestation",
            side_effect=AssertionError("fallback used despite a valid signature"),
        ):
            self.assertEqual(loop.resolve_semantic_attestation(ATTESTATION_ID), RECEIPT)

    def test_fallback_is_disabled_by_default(self) -> None:
        receipt, _ = self._paths()
        receipt.write_bytes(loop._canonical_json_bytes(RECEIPT) + b"\n")
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {},
            clear=False,
        ):
            os.environ.pop("Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK", None)
            self.assert_code(
                "CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_MISSING",
                loop.resolve_semantic_attestation,
                ATTESTATION_ID,
            )

    def test_fallback_does_not_mask_invalid_signature(self) -> None:
        self._write_bundle(namespace="wrong-namespace")
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ):
            self.assert_code(
                "CONTROL_V9_OFFLINE_ATTESTATION_SIGNATURE_INVALID",
                loop.resolve_semantic_attestation,
                ATTESTATION_ID,
            )

    def test_fallback_rejects_noncanonical_receipt(self) -> None:
        receipt, _ = self._paths()
        receipt.write_text(json.dumps(RECEIPT, indent=2) + "\n", encoding="utf-8")
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ):
            self.assert_code(
                "SEMANTIC_ATTESTATION_INVALID",
                loop.resolve_semantic_attestation,
                ATTESTATION_ID,
            )

    def test_fallback_is_darwin_only(self) -> None:
        receipt, _ = self._paths()
        receipt.write_bytes(loop._canonical_json_bytes(RECEIPT) + b"\n")
        with mock.patch.object(loop.sys, "platform", "linux"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ), mock.patch.object(
            loop,
            "resolve_linux_semantic_attestation",
            return_value=None,
        ):
            self.assertIsNone(loop.resolve_semantic_attestation(ATTESTATION_ID))

    def test_explicit_fallback_recovers_missing_root_trust(self) -> None:
        self._write_bundle()
        self.allowed.unlink()
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ):
            self.assertEqual(loop.resolve_semantic_attestation(ATTESTATION_ID), RECEIPT)

    def test_invalid_fallback_switch_fails_closed(self) -> None:
        receipt, _ = self._paths()
        receipt.write_bytes(loop._canonical_json_bytes(RECEIPT) + b"\n")
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "true"},
        ):
            self.assert_code(
                "CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK_INVALID",
                loop.resolve_semantic_attestation,
                ATTESTATION_ID,
            )

    def test_fallback_does_not_bypass_revocation(self) -> None:
        self._write_bundle()
        self._write_revocations([ATTESTATION_ID])
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ):
            self.assert_code(
                "CONTROL_V9_OFFLINE_ATTESTATION_ID_REVOKED",
                loop.resolve_semantic_attestation,
                ATTESTATION_ID,
            )

    def test_fallback_without_signature_honors_tracked_revocation(self) -> None:
        receipt, _ = self._paths()
        receipt.write_bytes(loop._canonical_json_bytes(RECEIPT) + b"\n")
        self._write_tracked_revocations([ATTESTATION_ID])
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ):
            self.assert_code(
                "CONTROL_V9_OFFLINE_ATTESTATION_ID_REVOKED",
                loop.resolve_semantic_attestation,
                ATTESTATION_ID,
            )

    def test_fallback_does_not_mask_unsafe_trust_permissions(self) -> None:
        self._write_bundle()
        self.allowed.chmod(0o620)
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ):
            self.assert_code(
                "CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID",
                loop.resolve_semantic_attestation,
                ATTESTATION_ID,
            )

    def test_fallback_does_not_mask_symlinked_signature(self) -> None:
        receipt, signature = self._paths()
        receipt.write_bytes(loop._canonical_json_bytes(RECEIPT) + b"\n")
        target = self.root / "signature-target"
        target.write_text("not a signature\n", encoding="utf-8")
        signature.symlink_to(target)
        with mock.patch.object(loop.sys, "platform", "darwin"), mock.patch.dict(
            os.environ,
            {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
        ):
            self.assert_code(
                "CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_INVALID",
                loop.resolve_semantic_attestation,
                ATTESTATION_ID,
            )

    def test_fallback_rejects_symlinked_bundle_directory(self) -> None:
        real_bundle = self.root / "real-bundle"
        real_bundle.mkdir()
        receipt = real_bundle / f"{ATTESTATION_ID}.receipt.json"
        receipt.write_bytes(loop._canonical_json_bytes(RECEIPT) + b"\n")
        tracked_revocations = real_bundle / "semantic_attestation_revoked_ids.v1.json"
        tracked_revocations.write_bytes(
            loop._canonical_json_bytes(
                {
                    "schema": "q3_semantic_attestation_revocations.v1",
                    "revoked_attestation_ids": [],
                }
            )
            + b"\n"
        )
        linked_bundle = self.root / "linked-bundle"
        linked_bundle.symlink_to(real_bundle, target_is_directory=True)
        with (
            mock.patch.object(loop, "SIGNED_OFFLINE_BUNDLE_DIR", linked_bundle),
            mock.patch.object(loop.sys, "platform", "darwin"),
            mock.patch.dict(
                os.environ,
                {"Q3_CONTROL_V9_MAC_TRACKED_RECEIPT_FALLBACK": "1"},
            ),
        ):
            self.assert_code(
                "CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_INVALID",
                loop.resolve_semantic_attestation,
                ATTESTATION_ID,
            )

    def test_missing_receipt_fails_closed(self) -> None:
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_MISSING",
            loop.resolve_signed_offline_semantic_attestation,
            ATTESTATION_ID,
        )

    def test_missing_signature_fails_closed(self) -> None:
        receipt, _ = self._paths()
        receipt.write_bytes(loop._canonical_json_bytes(RECEIPT) + b"\n")
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_MISSING",
            loop.resolve_signed_offline_semantic_attestation,
            ATTESTATION_ID,
        )

    def test_one_byte_receipt_mutation_fails_signature(self) -> None:
        receipt, _ = self._write_bundle()
        receipt.write_bytes(receipt.read_bytes().replace(b"PLANT_SCOPE", b"PLANT_SCOPF"))
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_SIGNATURE_INVALID",
            loop.resolve_signed_offline_semantic_attestation,
            ATTESTATION_ID,
        )

    def test_signature_by_unpinned_key_fails(self) -> None:
        other = self.root / "other"
        subprocess.run(
            ["/usr/bin/ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", str(other)],
            check=True,
        )
        self._write_bundle(key=other)
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_SIGNATURE_INVALID",
            loop.resolve_signed_offline_semantic_attestation,
            ATTESTATION_ID,
        )

    def test_wrong_principal_fails_trust(self) -> None:
        self._write_bundle()
        self._write_allowed_signers(self.key, principal="OTHER_AUDITOR")
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID",
            loop.resolve_signed_offline_semantic_attestation,
            ATTESTATION_ID,
        )

    def test_wrong_signature_namespace_fails(self) -> None:
        self._write_bundle(namespace="wrong-namespace")
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_SIGNATURE_INVALID",
            loop.resolve_signed_offline_semantic_attestation,
            ATTESTATION_ID,
        )

    def test_group_writable_trust_file_fails(self) -> None:
        self._write_bundle()
        self.allowed.chmod(0o620)
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID",
            loop.resolve_signed_offline_semantic_attestation,
            ATTESTATION_ID,
        )

    def test_symlinked_trust_or_revocation_file_fails(self) -> None:
        self._write_bundle()
        for attribute, path in (
            ("SIGNED_OFFLINE_ALLOWED_SIGNERS", self.allowed),
            ("SIGNED_OFFLINE_REVOCATIONS", self.revocations),
        ):
            link = self.trust / f"{path.name}.link"
            link.symlink_to(path)
            with self.subTest(attribute=attribute), mock.patch.object(loop, attribute, link):
                self.assert_code(
                    "CONTROL_V9_OFFLINE_ATTESTATION_TRUST_INVALID",
                    loop.resolve_signed_offline_semantic_attestation,
                    ATTESTATION_ID,
                )

    def test_revoked_id_fails_despite_valid_signature(self) -> None:
        self._write_bundle()
        self._write_revocations([ATTESTATION_ID])
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_ID_REVOKED",
            loop.resolve_signed_offline_semantic_attestation,
            ATTESTATION_ID,
        )

    def test_signed_receipt_field_drift_fails_exact_validator(self) -> None:
        drifted = dict(RECEIPT, normalization="drifted")
        self._write_bundle(drifted)
        self.assert_code(
            "SEMANTIC_ATTESTATION_INVALID",
            loop._validate_semantic_attestation,
            self._entry(RECEIPT),
            resolver=loop.resolve_signed_offline_semantic_attestation,
            supplier_preflight_resolver=None,
        )

    def test_unsigned_tracked_json_never_resolves(self) -> None:
        receipt, _ = self._paths()
        receipt.write_bytes(loop._canonical_json_bytes(RECEIPT) + b"\n")
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_BUNDLE_MISSING",
            loop.resolve_signed_offline_semantic_attestation,
            ATTESTATION_ID,
        )

    def test_no_caller_path_or_environment_override(self) -> None:
        signature = inspect.signature(loop.resolve_signed_offline_semantic_attestation)
        self.assertEqual(list(signature.parameters), ["attestation_id"])
        self._write_bundle()
        with mock.patch.dict(os.environ, {"Q3_ATTESTATION_PATH": "/tmp/forged"}):
            self.assertEqual(
                loop.resolve_signed_offline_semantic_attestation(ATTESTATION_ID), RECEIPT
            )

    def test_validation_does_not_edit_quarantine_state(self) -> None:
        self._write_bundle()
        entry = self._entry(RECEIPT)
        before = json.dumps(entry, sort_keys=True).encode()
        loop._validate_semantic_attestation(
            entry,
            resolver=loop.resolve_signed_offline_semantic_attestation,
            supplier_preflight_resolver=None,
        )
        self.assertEqual(json.dumps(entry, sort_keys=True).encode(), before)

    def test_one_valid_and_one_missing_bundle_fails_whole_state(self) -> None:
        repo = self.root / "repo"
        (repo / "docs/Codex").mkdir(parents=True)
        (repo / "Q3").mkdir()
        task_path = repo / "docs/Codex/TASK.md"
        source_path = repo / "Q3/Plant.lean"
        task_path.write_text("# plant task\n", encoding="utf-8")
        source_path.write_text("theorem plant : True := by trivial\n", encoding="utf-8")
        subprocess.run(["git", "init", "-q", "-b", "rh_clean"], cwd=repo, check=True)
        subprocess.run(["git", "config", "user.name", "Plant"], cwd=repo, check=True)
        subprocess.run(
            ["git", "config", "user.email", "plant@example.invalid"], cwd=repo, check=True
        )
        subprocess.run(["git", "add", "."], cwd=repo, check=True)
        subprocess.run(["git", "commit", "-q", "-m", "fixture"], cwd=repo, check=True)

        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=repo, check=True, capture_output=True, text=True
        ).stdout.strip()
        task_blob = subprocess.run(
            ["git", "rev-parse", "HEAD:docs/Codex/TASK.md"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        source_blob = subprocess.run(
            ["git", "rev-parse", "HEAD:Q3/Plant.lean"],
            cwd=repo,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()

        first = dict(
            RECEIPT,
            task_blob=task_blob,
            source_commit=head,
            source_git_blob=source_blob,
        )
        second = dict(first, attestation_id="ATTEST_SIGNED_OFFLINE_PLANT_V2")
        self._write_bundle(first)
        first_entry = self._entry(first, entry_id="ENTRY_SIGNED_OFFLINE_PLANT_ONE")
        second_entry = self._entry(second, entry_id="ENTRY_SIGNED_OFFLINE_PLANT_TWO")
        state = {
            "schema": "q3_semantic_quarantine.v1",
            "control_version": 9,
            "entries": [first_entry, second_entry],
            "event_ledger": [],
            "tactical_repairs": [],
            "active_lease": None,
        }
        self.assert_code(
            "CONTROL_V9_OFFLINE_ATTESTATION_ALL_ENTRY_VALIDATION_FAILED",
            loop.validate_state,
            state,
            repo_root=repo,
            semantic_attestation_resolver=loop.resolve_signed_offline_semantic_attestation,
        )


if __name__ == "__main__":
    unittest.main()
