#!/usr/bin/env python3
"""Verify Q28 raw request and nine full source bodies. No mathematical certification."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

EXPECTED_NAME = 'PROSHKA_CCM_ORIGINAL_P_SIGNED_RESIDUE_Q28_2026-10-26.txt'
EXPECTED_BYTES = 199411
EXPECTED_LF = 2681
EXPECTED_HASH = 'cb34557c531175821de798478fb433b2834c4e6a6092ed572664fc5855a36423'

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def main(path: Path) -> None:
    raw = path.read_bytes()
    assert len(raw) == EXPECTED_BYTES, ('request bytes', len(raw))
    assert raw.count(b'\n') == EXPECTED_LF, ('request LF', raw.count(b'\n'))
    assert sha(raw) == EXPECTED_HASH, ('request hash', sha(raw))
    raw.decode('utf-8')  # strict, no repair or normalization
    head = raw[:raw.index(b'BEGIN_SOURCE S1 ')]
    pattern = rb'^(S\d+): ([^\n]+?) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$'
    rows = re.findall(pattern, head, re.M)
    assert len(rows) == 9
    results = []
    last_end = 0
    for sid, source_path, size_raw, hash_raw in rows:
        marker = b'BEGIN_SOURCE ' + sid + b' ' + source_path + b'\n'
        start = raw.index(marker, last_end) + len(marker)
        size = int(size_raw)
        body = raw[start:start+size]
        body.decode('utf-8')
        assert len(body) == size
        assert sha(body) == hash_raw.decode()
        end_marker = b'\nEND_SOURCE ' + sid
        assert raw[start+size:start+size+len(end_marker)] == end_marker
        last_end = start+size+len(end_marker)
        results.append({
            'id': sid.decode(), 'path': source_path.decode(), 'bytes': size,
            'sha256': sha(body), 'lf': body.count(b'\n'), 'match': True,
        })
    print(json.dumps({
        'request': {'name': EXPECTED_NAME, 'bytes': len(raw),
                    'lf': raw.count(b'\n'), 'sha256': sha(raw), 'match': True},
        'source_count': len(results), 'sources': results,
        'scope': 'Raw transport and body integrity only; not a proof or independent audit.'
    }, ensure_ascii=False, indent=2, sort_keys=True))

if __name__ == '__main__':
    target = Path(sys.argv[1]) if len(sys.argv)>1 else Path('/mnt/data')/EXPECTED_NAME
    main(target)
