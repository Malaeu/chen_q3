"""Control-v9 external semantic-attestation broker.

The Linux body is the independent semantic auditor.  Attestations it issues
live outside the repository, so no committing body can mint or edit one.  This
process exposes them read-only over one fixed Unix-domain socket.

What this broker deliberately cannot do:

* it never accepts a receipt from a caller — the only exposed operation is
  lookup by attestation ID;
* it never reads a caller-selected path;
* it never issues an attestation on request: issuing is a separate local
  command run by the auditor, not an exposed socket operation.

If the broker is unavailable, resolution fails and admission fails closed.
"""

from __future__ import annotations

import json
import os
import socket
import socketserver
import sys
from pathlib import Path
from typing import Any

SOCKET_PATH = Path("/run/q3-control-v9/semantic-attestation.sock")
REGISTRY_DIR = Path.home() / ".local" / "share" / "q3-control-v9" / "receipts"

QUERY_SCHEMA = "q3_semantic_attestation_query.v1"
RESPONSE_SCHEMA = "q3_semantic_attestation.v1"
ISSUER = "LINUX_INDEPENDENT_SEMANTIC_AUDITOR"

MAX_QUERY_BYTES = 4096
ATTESTATION_ID_MAX = 256


def _safe_attestation_id(value: Any) -> str | None:
    """Accept only a flat identifier, so a query can never name a path."""
    if not isinstance(value, str) or not value:
        return None
    if len(value) > ATTESTATION_ID_MAX:
        return None
    if not all(char.isalnum() or char in "_-." for char in value):
        return None
    if value.startswith(".") or "/" in value or "\\" in value:
        return None
    return value


def lookup(attestation_id: str, *, registry_dir: Path = REGISTRY_DIR) -> dict[str, Any] | None:
    """Return the stored receipt for this exact ID, or None."""
    safe = _safe_attestation_id(attestation_id)
    if safe is None:
        return None
    path = registry_dir / f"{safe}.json"
    if not path.is_file():
        return None
    try:
        receipt = json.loads(path.read_bytes())
    except (OSError, ValueError):
        return None
    if not isinstance(receipt, dict):
        return None
    if receipt.get("schema") != RESPONSE_SCHEMA:
        return None
    if receipt.get("attestation_id") != safe:
        return None
    if receipt.get("issuer") != ISSUER:
        return None
    return receipt


class _Handler(socketserver.StreamRequestHandler):
    timeout = 5

    def handle(self) -> None:
        raw = self.rfile.readline(MAX_QUERY_BYTES)
        try:
            query = json.loads(raw)
        except ValueError:
            self._respond(None)
            return
        if not isinstance(query, dict) or query.get("schema") != QUERY_SCHEMA:
            self._respond(None)
            return
        extra = set(query) - {"schema", "attestation_id"}
        if extra:
            self._respond(None)
            return
        # Read the registry location at call time, not at import time.
        self._respond(lookup(query.get("attestation_id"), registry_dir=REGISTRY_DIR))

    def _respond(self, receipt: dict[str, Any] | None) -> None:
        body = json.dumps(
            {"schema": RESPONSE_SCHEMA, "receipt": receipt},
            ensure_ascii=False,
            sort_keys=True,
        )
        self.wfile.write(body.encode("utf-8") + b"\n")


class _Server(socketserver.ThreadingUnixStreamServer):
    daemon_threads = True
    allow_reuse_address = False


def serve(socket_path: Path = SOCKET_PATH) -> int:
    socket_path.parent.mkdir(parents=True, exist_ok=True)
    if socket_path.exists():
        # A stale socket from a dead broker is not a live broker.
        try:
            probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            probe.settimeout(1)
            probe.connect(str(socket_path))
            probe.close()
            print(f"broker already listening on {socket_path}", file=sys.stderr)
            return 1
        except OSError:
            socket_path.unlink()
    server = _Server(str(socket_path), _Handler)
    os.chmod(socket_path, 0o600)
    print(f"Q3_ATTESTATION_BROKER_LISTENING {socket_path}", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
        if socket_path.exists():
            socket_path.unlink()
    return 0


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if args and args[0] == "--socket":
        return serve(Path(args[1]))
    if args:
        print(f"unknown arguments: {args}", file=sys.stderr)
        return 2
    return serve()


if __name__ == "__main__":
    raise SystemExit(main())
