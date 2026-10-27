#!/usr/bin/env python3
"""Extract and replay Q53's four assets, never historical source scripts.
Usage: python3 replay_q53.py VERDICT.md CANONICAL_Q53.txt [OUTPUT_DIRECTORY]
Python 3.9+ standard library only.
"""
from __future__ import annotations
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HEADER = re.compile(
    rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\n'
    rb'SHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n', re.M)
EXPECTED = {'registration_q53.json', 'check_q53.py',
            'q53_checks.json', 'replay_q53.py'}


def extract(raw: bytes) -> dict[str, bytes]:
    assets = {}
    pos = 0
    while True:
        match = HEADER.search(raw, pos)
        if match is None:
            break
        name = match[1].decode('ascii')
        if name not in EXPECTED or name in assets:
            raise ValueError('unexpected or repeated asset: ' + name)
        start, end = match.end(), match.end() + int(match[2])
        body = raw[start:end]
        if len(body) != int(match[2]):
            raise ValueError('asset byte count: ' + name)
        if hashlib.sha256(body).hexdigest() != match[3].decode('ascii'):
            raise ValueError('asset SHA256: ' + name)
        body.decode('utf-8')
        close = b'```\nEND_ASSET\n'
        if raw[end:end + len(close)] != close:
            raise ValueError('asset closing frame: ' + name)
        assets[name] = body
        pos = end + len(close)
    if set(assets) != EXPECTED:
        raise ValueError('missing asset')
    return assets


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q53.py VERDICT.md CANONICAL_Q53.txt [OUTPUT_DIRECTORY]')
    verdict = Path(sys.argv[1]).resolve()
    canonical = Path(sys.argv[2]).resolve()
    out = Path(sys.argv[3] if len(sys.argv) == 4 else 'q53_replay').resolve()
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        target = out / name
        if target.resolve() in (verdict, canonical):
            raise ValueError('refusing to overwrite an input')
        target.write_bytes(body)
    run = subprocess.run(
        [sys.executable, str(out / 'check_q53.py'), str(canonical)],
        cwd=out, capture_output=True, check=True)
    (out / 'check_q53.stdout').write_bytes(run.stdout)
    if (out / 'q53_checks.json').read_bytes() != assets['q53_checks.json']:
        raise ValueError('replayed JSON differs from the embedded result')
    print(json.dumps(dict(asset_count=len(assets), all_asset_hashes_match=True,
                          checker_executed=True, json_byte_identical=True,
                          historical_programs_executed=False,
                          independent_audit=False, production_spectrum=False),
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
