#!/usr/bin/env python3
"""Extract Q48's seven new assets and replay both recorded algebra stages.
Usage: python3 replay_q48.py VERDICT.md CANONICAL_Q48.txt [OUTPUT_DIRECTORY]
No historical code from the canonical TXT is executed. Standard library only.
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
EXPECTED = {
    'registration_q48.json', 'refinement_registration_q48.json',
    'check_q48_initial.py', 'q48_checks_initial.json',
    'check_q48.py', 'q48_checks.json', 'replay_q48.py',
}

def extract(raw: bytes) -> dict[str, bytes]:
    assets: dict[str, bytes] = {}
    pos = 0
    while True:
        h = HEADER.search(raw, pos)
        if h is None:
            break
        name = h[1].decode('ascii')
        start = h.end()
        end = start + int(h[2])
        body = raw[start:end]
        if name in assets:
            raise ValueError('duplicate asset: ' + name)
        if len(body) != int(h[2]) or hashlib.sha256(body).hexdigest() != h[3].decode():
            raise ValueError('asset size/hash: ' + name)
        suffix = b'```\nEND_ASSET\n'
        if raw[end:end+len(suffix)] != suffix:
            raise ValueError('asset framing: ' + name)
        assets[name] = body
        pos = end + len(suffix)
    if set(assets) != EXPECTED:
        raise ValueError('unexpected asset set')
    return assets

def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: python3 replay_q48.py VERDICT.md CANONICAL_Q48.txt [OUTPUT_DIRECTORY]')
    verdict = Path(sys.argv[1]).resolve()
    canonical = Path(sys.argv[2]).resolve()
    out = Path(sys.argv[3] if len(sys.argv) == 4 else 'q48_replay').resolve()
    if not canonical.is_file():
        raise FileNotFoundError(canonical)
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True, exist_ok=True)
    for name, body in assets.items():
        (out / name).write_bytes(body)
    registration = json.loads(assets['refinement_registration_q48.json'])
    if hashlib.sha256(assets['check_q48_initial.py']).hexdigest() != registration['previous_checker_sha256']:
        raise ValueError('initial checker registration mismatch')
    if hashlib.sha256(assets['q48_checks_initial.json']).hexdigest() != registration['previous_results_sha256']:
        raise ValueError('initial result registration mismatch')
    runs = [('check_q48_initial.py', 'q48_checks_initial.json', 'initial_run'),
            ('check_q48.py', 'q48_checks.json', 'final_run')]
    for script, expected_json, directory in runs:
        wd = out / directory
        wd.mkdir(parents=True, exist_ok=True)
        proc = subprocess.run(
            [sys.executable, str(out/script), str(canonical)], cwd=wd,
            check=True, capture_output=True, text=True)
        (wd/'stdout.txt').write_text(proc.stdout, encoding='utf-8')
        if (wd/'q48_checks.json').read_bytes() != assets[expected_json]:
            raise ValueError('JSON mismatch: ' + expected_json)
    print(json.dumps({
        'asset_count': len(assets), 'all_asset_hashes_match': True,
        'registration_links_match': True, 'checker_runs': len(runs),
        'both_stage_json_byte_identical': True,
        'historical_source_programs_executed': False,
        'actual_original_P_numerical_spectra': False,
        'independent_audit': False,
    }, sort_keys=True, indent=2))

if __name__ == '__main__':
    main()
