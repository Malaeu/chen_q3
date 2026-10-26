#!/usr/bin/env python3
"""Verify the Q44 byte-framed packet. Does not run source-body code."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

EXPECTED_SHA = 'b92fc8dc125a9a363c7ae673ddfdf047045a7f5cbe75328b4a24f4d2d06dd0f9'
EXPECTED_BYTES = 149713
EXPECTED_LF = 2109
HEADER = re.compile(rb'^BEGIN_SOURCE (S\d+) ([^\n]+?) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n', re.M)

def verify(data: bytes) -> dict:
    if len(data) != EXPECTED_BYTES:
        raise ValueError('Whole-packet byte count differs')
    if data.count(b'\n') != EXPECTED_LF:
        raise ValueError('Whole-packet LF count differs')
    if hashlib.sha256(data).hexdigest() != EXPECTED_SHA:
        raise ValueError('Whole-packet SHA256 differs')
    data.decode('utf-8', errors='strict')
    rows, cursor = [], 0
    for i in range(1, 12):
        h = HEADER.search(data, cursor)
        if h is None or h[1] != f'S{i}'.encode():
            raise ValueError(f'Missing or out-of-order source S{i}')
        start, size, nlf = h.end(), int(h[3]), int(h[4])
        body = data[start:start + size]
        sha = hashlib.sha256(body).hexdigest()
        if len(body) != size or body.count(b'\n') != nlf or sha != h[5].decode():
            raise ValueError(f'Invalid body S{i}')
        body.decode('utf-8', errors='strict')
        marker = b'\nEND_SOURCE ' + h[1] + b'\n'
        end = start + size
        if data[end:end + len(marker)] != marker:
            raise ValueError(f'Invalid separator/end marker S{i}')
        first = data[:start].count(b'\n') + 1
        rows.append(dict(id=h[1].decode(), name=h[2].decode(), bytes=size,
                         lf=nlf, sha256=sha, first_line=first,
                         last_line=first + nlf - 1))
        cursor = end + len(marker)
    if HEADER.search(data, cursor):
        raise ValueError('Unexpected extra top-level source')
    return dict(file='PROSHKA_CCM_SOURCE_PAIR_NONCIRCULAR_MARGIN_Q44_2026-10-26.txt',
                bytes=len(data), lf=data.count(b'\n'), sha256=EXPECTED_SHA,
                source_count=len(rows), all_sources_verified=True,
                historical_code_executed=False, sources=rows)

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('packet', type=Path)
    ap.add_argument('--out', type=Path, default=Path('source_verification_q44.json'))
    args = ap.parse_args()
    data = args.packet.read_bytes()
    report = verify(data)
    corrupt = bytearray(data)
    first = HEADER.search(data)
    assert first is not None
    corrupt[first.end()] ^= 1
    try:
        verify(bytes(corrupt))
    except ValueError:
        report['planted_single_byte_corruption_detected'] = True
    else:
        raise AssertionError('A corrupted packet was accepted')
    text = json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + '\n'
    args.out.write_text(text, encoding='utf-8')
    print(text, end='')

if __name__ == '__main__':
    main()
