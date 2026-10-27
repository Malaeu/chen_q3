#!/usr/bin/env python3
"""Replay the four NEW Q56 assets, never historical programs.
Usage: python3 replay_q56.py VERDICT.md PACKET.txt [OUTPUT_DIRECTORY]
Python 3.9+, standard library only. Exact JSON must match byte for byte.
"""
from __future__ import annotations
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HEADER = re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n', re.M)
EXPECTED = {'registration_q56.json', 'check_q56.py', 'q56_checks.json', 'replay_q56.py'}


def extract(raw: bytes) -> dict:
    out = {}
    pos = 0
    while True:
        h = HEADER.search(raw, pos)
        if h is None:
            break
        name = h[1].decode('ascii')
        if name not in EXPECTED or name in out:
            raise ValueError('unexpected or duplicate asset: '+name)
        start, end = h.end(), h.end()+int(h[2])
        body = raw[start:end]
        if len(body) != int(h[2]) or hashlib.sha256(body).hexdigest() != h[3].decode():
            raise ValueError('asset bytes/hash: '+name)
        closing = b'```\nEND_ASSET\n'
        if raw[end:end+len(closing)] != closing:
            raise ValueError('asset closing frame: '+name)
        body.decode('utf-8')
        out[name] = body
        pos = end+len(closing)
    if set(out) != EXPECTED:
        raise ValueError('missing asset')
    return out


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q56.py VERDICT.md PACKET.txt [OUTPUT_DIRECTORY]')
    verdict, packet = (Path(s).resolve() for s in sys.argv[1:3])
    directory = Path(sys.argv[3] if len(sys.argv) == 4 else 'q56_replay').resolve()
    assets = extract(verdict.read_bytes())
    directory.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        target = directory/name
        if target.resolve() in (verdict, packet):
            raise ValueError('refusing to overwrite an input')
        target.write_bytes(body)
    result = directory/'q56_replayed.json'
    run = subprocess.run([sys.executable, str(directory/'check_q56.py'), str(packet), str(result)],
                         capture_output=True, check=True)
    (directory/'check_q56.stdout').write_bytes(run.stdout)
    if result.read_bytes() != assets['q56_checks.json']:
        raise ValueError('exact replay differs from embedded JSON')
    print(json.dumps(dict(asset_count=4, all_asset_hashes_match=True,
                          new_checker_executed=True, json_byte_identical=True,
                          historical_programs_executed=False,
                          independent_audit=False, production_spectrum=False,
                          interval_certificate=False), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
