#!/usr/bin/env python3
"""Verify the exact Q36 request and its twelve byte-locked source bodies."""
from pathlib import Path
import argparse
import hashlib
import json
import re

EXPECTED = 'be32d09c682a6993eba01dd8dea28a996c8b1f5a3c4c0879df4a05be17448d9e'

def verify(path):
    raw = Path(path).read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if (len(raw), raw.count(b'\n'), digest) != (140635, 2263, EXPECTED):
        raise ValueError('Canonical byte/LF/SHA mismatch')
    raw.decode('utf-8', errors='strict')
    pat = rb'^BEGIN_SOURCE (S\d+) ([^\n]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\nBODY:\n'
    rows = []
    for mt in re.finditer(pat, raw, re.M):
        sid, name, size, sha = mt.groups()
        size = int(size)
        body = raw[mt.end():mt.end()+size]
        got = hashlib.sha256(body).hexdigest()
        if len(body) != size or got != sha.decode():
            raise ValueError('Body hash mismatch: ' + sid.decode())
        if not raw[mt.end()+size:].startswith(b'\nEND_SOURCE\n'):
            raise ValueError('Body framing mismatch: ' + sid.decode())
        body.decode('utf-8', errors='strict')
        rows.append({'id':sid.decode(), 'name':name.decode(), 'bytes':size,
                     'lf':body.count(b'\n'), 'sha256':got,
                     'start_line':raw[:mt.end()].count(b'\n')+1,
                     'end_line':raw[:mt.end()+size].count(b'\n')})
    if [r['id'] for r in rows] != ['S'+str(i) for i in range(1,13)]:
        raise ValueError('Expected exactly S1 through S12')
    return {'request_bytes':len(raw), 'request_lf':raw.count(b'\n'),
            'request_sha256':digest, 'source_count':len(rows),
            'all_hashes_match':True, 'sources':rows}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('packet',type=Path)
    ap.add_argument('--output',type=Path,default=Path('q36_sources.json'))
    a=ap.parse_args()
    obj=verify(a.packet)
    a.output.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'source_count':obj['source_count'],'all_hashes_match':True}))

if __name__=='__main__':
    main()
