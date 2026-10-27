#!/usr/bin/env python3
"""Extract only the four NEW Q55 assets and reproduce their checks.
Usage: python3 replay_q55.py VERDICT.md PACKET.txt [OUTPUT_DIRECTORY]
Python 3.9+, standard library only. No historical source code is run.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HEADER = re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n',re.M)
EXPECTED = {'registration_q55.json','check_q55.py','q55_checks.json','replay_q55.py'}


def extract(raw: bytes) -> dict:
    assets = {}
    pos = 0
    while True:
        h = HEADER.search(raw,pos)
        if h is None:
            break
        name = h[1].decode('ascii')
        if name not in EXPECTED or name in assets:
            raise ValueError('unexpected/repeated asset: '+name)
        start, end = h.end(), h.end()+int(h[2])
        body = raw[start:end]
        if len(body) != int(h[2]) or hashlib.sha256(body).hexdigest() != h[3].decode():
            raise ValueError('asset size/hash: '+name)
        close = b'```\nEND_ASSET\n'
        if raw[end:end+len(close)] != close:
            raise ValueError('asset frame: '+name)
        body.decode('utf-8')
        assets[name] = body
        pos = end+len(close)
    if set(assets) != EXPECTED:
        raise ValueError('missing asset')
    return assets


def compare(expected: dict, actual: dict) -> None:
    # The source provenance, exact assertions and flags must agree exactly.
    for k in expected:
        if k != 'diagnostics' and expected[k] != actual.get(k):
            raise ValueError('exact replay mismatch: '+k)
    e,a = expected['diagnostics'],actual['diagnostics']
    for k in ('arithmetic','interval_certificate','planted_violations_detected','tolerance'):
        if e[k] != a[k]:
            raise ValueError('diagnostic metadata mismatch: '+k)
    if len(e['cases']) != len(a['cases']):
        raise ValueError('case count mismatch')
    for old,new in zip(e['cases'],a['cases']):
        for k in ('m','M','original_epsilon_schedule'):
            if old[k] != new[k]:
                raise ValueError('diagnostic case mismatch')
        for k in set(old)-{'m','M','original_epsilon_schedule'}:
            if abs(float(old[k])-float(new[k])) > 5e-11:
                raise ValueError('binary64 replay mismatch: '+k)
    # The executed checker itself enforces its 2e-11 residual tolerance.


def main() -> None:
    if len(sys.argv) not in (3,4):
        raise SystemExit('usage: python3 replay_q55.py VERDICT.md PACKET.txt [OUTPUT_DIRECTORY]')
    verdict,packet = (Path(x).resolve() for x in sys.argv[1:3])
    out = Path(sys.argv[3] if len(sys.argv)==4 else 'q55_replay').resolve()
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True,exist_ok=True)
    for name,body in assets.items():
        target = out/name
        if target.resolve() in (verdict,packet):
            raise ValueError('refusing to overwrite input')
        target.write_bytes(body)
    actual_path = out/'q55_replayed.json'
    run = subprocess.run([sys.executable,str(out/'check_q55.py'),str(packet),str(actual_path)],capture_output=True,check=True)
    (out/'check_q55.stdout').write_bytes(run.stdout)
    compare(json.loads(assets['q55_checks.json']),json.loads(actual_path.read_bytes()))
    result = dict(asset_count=4,all_asset_hashes_match=True,new_checker_executed=True,semantic_replay=True,json_byte_identical=actual_path.read_bytes()==assets['q55_checks.json'],historical_programs_executed=False,independent_audit=False,interval_certificate=False,production_spectrum=False)
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__ == '__main__':
    main()
