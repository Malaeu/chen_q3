#!/usr/bin/env python3
"""Verify the canonical byte-framed packet. Never execute historical code."""
from __future__ import annotations
from pathlib import Path
import argparse
import hashlib
import json
import re

HEADER = re.compile(rb'BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n')


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def inspect(data: bytes, expected: dict) -> dict:
    data.decode('utf-8', errors='strict')
    if len(data) != expected['bytes'] or data.count(b'\n') != expected['lf']:
        raise ValueError('Canonical packet byte/LF count differs')
    if digest(data) != expected['sha256']:
        raise ValueError('Canonical packet SHA256 differs')
    marker = b'BEGIN_SOURCE S1 '
    pos = data.find(marker)
    if pos < 0 or (pos and data[pos - 1] != 10):
        raise ValueError('Missing first source frame')
    measured = []
    for index, declared in enumerate(expected['sources'], 1):
        header = HEADER.match(data, pos)
        if header is None or header[1] != f'S{index}'.encode():
            raise ValueError(f'Unexpected source frame at {index}')
        start = header.end()
        end = start + int(header[3])
        body = data[start:end]
        body.decode('utf-8', errors='strict')
        row = {
            'id': header[1].decode(), 'name': header[2].decode(),
            'bytes': len(body), 'lf': body.count(b'\n'),
            'sha256': digest(body),
            'start_line': data[:start].count(b'\n') + 1,
            'end_line': data[:end].count(b'\n')
        }
        if len(body) != int(header[3]) or body.count(b'\n') != int(header[4]):
            raise ValueError(f'Body length differs: S{index}')
        if digest(body) != header[5].decode() or row != declared:
            raise ValueError(f'Body hash or manifest differs: S{index}')
        suffix = f'\nEND_SOURCE S{index}\n'.encode()
        if data[end:end + len(suffix)] != suffix:
            raise ValueError(f'Missing exact separator/end marker: S{index}')
        pos = end + len(suffix)
        while pos < len(data) and data[pos:pos+1] in (b'\n', b'\r', b' ', b'\t'):
            pos += 1
        measured.append(row)
    if pos != len(data):
        raise ValueError('Unparsed trailing material')
    return {
        'canonical_file': expected['file'],
        'canonical_bytes': len(data), 'canonical_lf': data.count(b'\n'),
        'canonical_sha256': digest(data),
        'source_count': len(measured),
        'all_bytes_lf_sha256_and_frames_match': True,
        'all_input_text_utf8': True,
        'historical_code_executed': False,
        'source_proofs_recertified_by_hashing': False
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('canonical_txt', type=Path)
    p.add_argument('--manifest', type=Path,
                   default=Path(__file__).with_name('q41_source_manifest.json'))
    args = p.parse_args()
    expected = json.loads(args.manifest.read_text(encoding='utf-8'))
    result = inspect(args.canonical_txt.read_bytes(), expected)
    text = json.dumps(result, sort_keys=True, indent=2) + '\n'
    Path('q41_source_verification.json').write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
