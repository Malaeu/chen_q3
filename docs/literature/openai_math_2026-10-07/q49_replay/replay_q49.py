#!/usr/bin/env python3
"""Extract and replay the four Q49 assets; do not execute historical sources.
Usage: python3 replay_q49.py VERDICT.md CANONICAL_Q49.txt [OUTPUT_DIRECTORY]
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
EXPECTED = {'registration_q49.json', 'check_q49.py',
            'q49_checks.json', 'replay_q49.py'}


def extract(raw: bytes) -> dict[str, bytes]:
    assets = {}
    pos = 0
    while True:
        hit = HEAD.search(raw, pos)
        if hit is None:
            break
        name = hit[1].decode('ascii')
        if name not in EXPECTED or name in assets:
            raise ValueError('unexpected or duplicate asset: ' + name)
        start = hit.end()
        end = start + int(hit[2])
        body = raw[start:end]
        if len(body) != int(hit[2]):
            raise ValueError('asset byte count: ' + name)
        if hashlib.sha256(body).hexdigest() != hit[3].decode('ascii'):
            raise ValueError('asset SHA-256: ' + name)
        body.decode('utf-8')
        suffix = b'```\nEND_ASSET\n'
        if raw[end:end+len(suffix)] != suffix:
            raise ValueError('asset frame: ' + name)
        assets[name] = body
        pos = end + len(suffix)
    if set(assets) != EXPECTED:
        raise ValueError('incomplete asset set')
    return assets


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit(
            'usage: python3 replay_q49.py VERDICT.md CANONICAL_Q49.txt [OUTPUT_DIRECTORY]')
    verdict = Path(sys.argv[1]).resolve()
    canonical = Path(sys.argv[2]).resolve()
    out = Path(sys.argv[3] if len(sys.argv) == 4 else 'q49_replay').resolve()
    if not canonical.is_file():
        raise FileNotFoundError(canonical)
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        target = out / name
        if target.is_symlink():
            raise ValueError('refusing symlink output: ' + str(target))
        target.write_bytes(body)
    run = subprocess.run(
        [sys.executable, str(out / 'check_q49.py'), str(canonical)],
        cwd=out, capture_output=True, text=True, check=True)
    (out / 'check_q49.stdout').write_text(run.stdout, encoding='utf-8')
    if (out / 'q49_checks.json').read_bytes() != assets['q49_checks.json']:
        raise ValueError('replayed JSON differs from the embedded output')
    result = dict(asset_count=len(assets), all_asset_hashes_verified=True,
                  checker_run=True, checker_result_byte_identical=True,
                  historical_source_programs_executed=False,
                  production_CCM_spectrum_run=False,
                  independent_mathematical_review=False)
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
