#!/usr/bin/env python3
"""Verify the byte-locked Q26 packet and every complete source body.
Usage: python verify_sources_q26.py [path-to-canonical-Q26.txt]
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

DEFAULT = 'PROSHKA_CCM_ACTUAL_SOURCE_RIGIDITY_Q26_2026-10-25.txt'
EXPECTED_BYTES = 256003
EXPECTED_LF = 3711
EXPECTED_SHA = '994af0521c42fbe7c00211959fcb0dd630c107fd559a1edd6e40e9a287b3da10'
path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(DEFAULT)
raw = path.read_bytes()
assert len(raw) == EXPECTED_BYTES
assert raw.count(b'\n') == EXPECTED_LF
assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA
raw.decode('utf-8', errors='strict')
head = raw[:raw.index(b'BEGIN_SOURCE S1 ')]
rows = re.findall(rb'^(S\d+): (.+?) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$', head, re.M)
assert len(rows) == 12
out = []
for sid, src, size, sha in rows:
    marker = b'BEGIN_SOURCE ' + sid + b' ' + src + b'\n'
    assert raw.count(marker) == 1
    start = raw.index(marker) + len(marker)
    body = raw[start:start + int(size)]
    assert hashlib.sha256(body).hexdigest().encode() == sha
    suffix = b'\nEND_SOURCE ' + sid + b'\n'
    assert raw[start + int(size):].startswith(suffix)
    out.append({'id':sid.decode(),'path':src.decode(),'bytes':len(body),'sha256':sha.decode()})
print(json.dumps({'request_bytes':len(raw),'request_lf':raw.count(b'\n'),
                  'request_sha256':hashlib.sha256(raw).hexdigest(),
                  'sources_verified':len(out),'sources':out},ensure_ascii=False,indent=2,sort_keys=True))
