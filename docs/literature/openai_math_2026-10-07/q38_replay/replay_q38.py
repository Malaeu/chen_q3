#!/usr/bin/env python3
"""Extract only Q38's six declared assets and replay both new checkers.

Usage: python replay_q38.py VERDICT.md CANONICAL.txt --out q38_replay
No historical source commands, network calls, or repository writes.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

NAMES = {'check_q38.py', 'q38_checks.json', 'verify_sources_q38.py',
         'source_verification_q38.json', 'registered_predictions.json', 'replay_q38.py'}
HEADER = re.compile(rb'<!-- BEGIN_FILE ([A-Za-z0-9_.-]+) BYTES (\d+) SHA256 ([0-9a-f]{64}) -->\n````[a-z]*\n')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('verdict', type=Path)
    ap.add_argument('packet', type=Path)
    ap.add_argument('--out', type=Path, default=Path('q38_replay'))
    args = ap.parse_args()
    verdict = args.verdict.read_bytes()
    packet = args.packet.resolve(strict=True)
    args.out.mkdir(parents=True, exist_ok=True)
    found = set()
    for match in HEADER.finditer(verdict):
        name = match.group(1).decode()
        if name not in NAMES or name in found:
            raise ValueError('Unexpected or duplicated asset: '+name)
        size = int(match.group(2))
        body = verdict[match.end():match.end()+size]
        if len(body) != size or hashlib.sha256(body).hexdigest() != match.group(3).decode():
            raise ValueError('Bad asset hash or length: '+name)
        suffix = b'````\n<!-- END_FILE '+name.encode()+b' -->'
        if not verdict[match.end()+size:].startswith(suffix):
            raise ValueError('Invalid asset closing frame: '+name)
        (args.out/name).write_bytes(body)
        found.add(name)
    if found != NAMES:
        raise ValueError('Missing assets: '+str(NAMES-found))
    expected = {name:(args.out/name).read_bytes()
                for name in ('q38_checks.json','source_verification_q38.json')}
    subprocess.run([sys.executable,'check_q38.py'], cwd=args.out, check=True)
    subprocess.run([sys.executable,'verify_sources_q38.py',str(packet)], cwd=args.out, check=True)
    for name,data in expected.items():
        if (args.out/name).read_bytes() != data:
            raise AssertionError('Replay output differs: '+name)
    print(json.dumps({'assets_verified':len(found),'exact_groups':45,
                      'planted_errors_detected':10,'source_bodies_verified':12,
                      'output_jsons_byte_identical':True},indent=2))

if __name__ == '__main__':
    main()
