#!/usr/bin/env python3
"""Extract and replay only the four Q46 assets from the full verdict.
Usage: python3 replay_q46.py VERDICT.md CANONICAL_Q46.txt [OUTPUT_DIRECTORY]
No historical program in the canonical packet is executed.
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
EXPECTED = {'registration_q46.json', 'check_q46.py',
            'q46_checks.json', 'replay_q46.py'}


def extract(raw: bytes) -> dict[str, bytes]:
    pos = 0
    assets = {}
    while True:
        hit = HEAD.search(raw, pos)
        if hit is None:
            break
        name = hit[1].decode('ascii')
        size = int(hit[2])
        start = hit.end()
        end = start + size
        body = raw[start:end]
        if name in assets:
            raise ValueError('duplicate asset: ' + name)
        if len(body) != size or hashlib.sha256(body).hexdigest() != hit[3].decode():
            raise ValueError('asset length/hash mismatch: ' + name)
        suffix = b'```\nEND_ASSET\n'
        if raw[end:end + len(suffix)] != suffix:
            raise ValueError('asset boundary mismatch: ' + name)
        assets[name] = body
        pos = end + len(suffix)
    if set(assets) != EXPECTED:
        raise ValueError('unexpected asset set')
    return assets


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q46.py VERDICT.md CANONICAL_Q46.txt [OUTPUT_DIRECTORY]')
    verdict = Path(sys.argv[1]).resolve()
    canonical = Path(sys.argv[2]).resolve()
    out = Path(sys.argv[3] if len(sys.argv) == 4 else 'q46_replay').resolve()
    if not canonical.is_file():
        raise FileNotFoundError(canonical)
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        (out / name).write_bytes(body)
    run = subprocess.run(
        [sys.executable, str(out / 'check_q46.py'), str(canonical)],
        cwd=out, check=True, capture_output=True, text=True)
    (out / 'check_q46.stdout').write_text(run.stdout, encoding='utf-8')
    if (out / 'q46_checks.json').read_bytes() != assets['q46_checks.json']:
        raise ValueError('reproduced JSON differs from the embedded result')
    result = {
        'all_asset_hashes_match': True,
        'asset_count': len(assets),
        'checker_run': True,
        'historical_programs_executed': False,
        'output_byte_identical': True,
        'production_spectrum_run': False,
    }
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
