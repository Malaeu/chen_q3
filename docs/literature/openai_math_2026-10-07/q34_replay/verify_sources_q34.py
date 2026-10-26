#!/usr/bin/env python3
"""Verify the exact Q34 request and all nine size-locked UTF-8 bodies."""
import argparse
import hashlib
import json
import re
from pathlib import Path

EXPECTED = 'bb135a92b766d6715599ce64627f8333b492cce3ee2e7ae9b8294da9beb0e037'

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def verify(path: Path) -> dict:
    raw = path.read_bytes()
    if len(raw) != 123546 or raw.count(b'\n') != 2044 or digest(raw) != EXPECTED:
        raise ValueError('Q34 request length, LF or SHA256 mismatch')
    raw.decode('utf-8', errors='strict')
    pattern = rb'^BEGIN_SOURCE (S\d+) ([^\n]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\nBODY:\n'
    records = []
    for match in re.finditer(pattern, raw, re.M):
        sid, name, size, sha = match.groups()
        size = int(size)
        start, end = match.end(), match.end() + size
        body = raw[start:end]
        if len(body) != size or digest(body) != sha.decode():
            raise ValueError('Body mismatch: ' + sid.decode())
        if not raw[end:].startswith(b'\nEND_SOURCE\n'):
            raise ValueError('Wrong separator or body boundary: ' + sid.decode())
        body.decode('utf-8', errors='strict')
        records.append({'id': sid.decode(), 'name': name.decode(), 'bytes': size,
                        'lf': body.count(b'\n'), 'sha256': digest(body)})
    if [x['id'] for x in records] != [f'S{i}' for i in range(1, 10)]:
        raise ValueError('Source IDs or count do not match S1--S9')
    return {'request_bytes': len(raw), 'request_lf': raw.count(b'\n'),
            'request_sha256': digest(raw), 'source_count': len(records),
            'all_hashes_match': True, 'sources': records}

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('packet', type=Path)
    parser.add_argument('--output', type=Path, default=Path('q34_sources.json'))
    args = parser.parse_args()
    output = verify(args.packet)
    args.output.write_text(json.dumps(output, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'source_count': output['source_count'], 'all_hashes_match': True}))

if __name__ == '__main__':
    main()
