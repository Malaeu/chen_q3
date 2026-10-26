#!/usr/bin/env python3
"""Verify the canonical Q38 bytes and all twelve size-locked source bodies.

Run: python verify_sources_q38.py PROSHKA_CCM_SQUAREFREE_SIGNED_RETURN_Q38_2026-10-26.txt
Only reads the supplied packet and writes source_verification_q38.json.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

EXPECTED_NAME = 'PROSHKA_CCM_SQUAREFREE_SIGNED_RETURN_Q38_2026-10-26.txt'
EXPECTED_BYTES = 215599
EXPECTED_LF = 3497
EXPECTED_SHA = '173dddc9e6e3904b2d6d413d61f841a00c19dcf73774cd0a4629cce5215c376e'
HEADER = re.compile(rb'^BEGIN_SOURCE (S\d+) ([^\n]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\nBODY:\n', re.M)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('packet', nargs='?', type=Path, default=Path(EXPECTED_NAME))
    args = parser.parse_args()
    data = args.packet.read_bytes()
    data.decode('utf-8', errors='strict')
    sha = hashlib.sha256(data).hexdigest()
    if (len(data), data.count(b'\n'), sha) != (EXPECTED_BYTES, EXPECTED_LF, EXPECTED_SHA):
        raise ValueError('Canonical request byte count, LF count, or SHA-256 differs')
    records = []
    pos = 0
    for index in range(1, 13):
        match = HEADER.search(data, pos)
        if match is None or match.group(1) != ('S%d' % index).encode():
            raise ValueError('Missing or out-of-order source %d' % index)
        size = int(match.group(3))
        begin = match.end()
        end = begin + size
        body = data[begin:end]
        body.decode('utf-8', errors='strict')
        digest = hashlib.sha256(body).hexdigest()
        if len(body) != size or digest != match.group(4).decode():
            raise ValueError('Body bytes or SHA differ: ' + match.group(1).decode())
        if not data[end:].startswith(b'\nEND_SOURCE\n'):
            raise ValueError('Invalid separator or end marker')
        first = data[:begin].count(b'\n') + 1
        records.append(dict(id=match.group(1).decode(), name=match.group(2).decode(),
                            bytes=size, lf=body.count(b'\n'), sha256=digest,
                            start_line=first, end_line=first+body.count(b'\n')-1))
        pos = end + len(b'\nEND_SOURCE\n')
    if HEADER.search(data, pos) is not None:
        raise ValueError('Unexpected extra source body')
    out = dict(status='EXACT_BYTES_VERIFIED_NOT_MATHEMATICAL_CERTIFICATION',
               request=EXPECTED_NAME, bytes=len(data), lf=data.count(b'\n'),
               sha256=sha, source_count=len(records), sources=records)
    Path('source_verification_q38.json').write_text(
        json.dumps(out, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'bytes':len(data),'lf':data.count(b'\n'),'sources':len(records),'sha256':sha}))

if __name__ == '__main__':
    main()
