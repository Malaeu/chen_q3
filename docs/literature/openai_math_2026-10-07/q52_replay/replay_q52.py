#!/usr/bin/env python3
"""Extract and replay Q52's four checked assets; do not run source bodies.
Usage: python3 replay_q52.py VERDICT.md CANONICAL_Q52.txt [OUTPUT_DIRECTORY]
Only Python 3.9+ standard-library modules are required.
"""
from __future__ import annotations
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HEAD = re.compile(
    rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\n'
    rb'SHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n', re.M)
EXPECTED = {'registration_q52.json', 'check_q52.py',
            'q52_checks.json', 'replay_q52.py'}


def extract(raw: bytes) -> dict[str, bytes]:
    assets = {}
    pos = 0
    while True:
        h = HEAD.search(raw, pos)
        if h is None:
            break
        name = h[1].decode('ascii')
        if name not in EXPECTED or name in assets:
            raise ValueError('unexpected or duplicate asset: ' + name)
        start, end = h.end(), h.end() + int(h[2])
        body = raw[start:end]
        if len(body) != int(h[2]):
            raise ValueError('asset length: ' + name)
        if hashlib.sha256(body).hexdigest() != h[3].decode('ascii'):
            raise ValueError('asset SHA256: ' + name)
        body.decode('utf-8')
        closing = b'```\nEND_ASSET\n'
        if raw[end:end+len(closing)] != closing:
            raise ValueError('asset closing frame: ' + name)
        assets[name] = body
        pos = end + len(closing)
    if set(assets) != EXPECTED:
        raise ValueError('missing assets')
    return assets


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q52.py VERDICT.md CANONICAL_Q52.txt [OUTPUT_DIRECTORY]')
    verdict, canonical = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    out = Path(sys.argv[3] if len(sys.argv) == 4 else 'q52_replay').resolve()
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        target = out / name
        if target.resolve() in (verdict, canonical):
            raise ValueError('refusing to overwrite an input')
        target.write_bytes(body)
    completed = subprocess.run(
        [sys.executable, str(out / 'check_q52.py'), str(canonical)],
        cwd=out, capture_output=True, check=True)
    (out / 'check_q52.stdout').write_bytes(completed.stdout)
    if (out / 'q52_checks.json').read_bytes() != assets['q52_checks.json']:
        raise ValueError('replayed JSON differs from the embedded result')
    report = dict(asset_count=len(assets), all_asset_hashes_match=True,
                  checker_executed=True, json_byte_identical=True,
                  historical_programs_executed=False, production_spectrum=False,
                  independent_audit=False)
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
