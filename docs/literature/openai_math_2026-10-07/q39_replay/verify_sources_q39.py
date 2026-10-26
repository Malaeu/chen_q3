#!/usr/bin/env python3
"""Verify the canonical Q39 bytes and top-level byte-locked bodies.
Run: python verify_sources_q39.py /path/to/canonical_Q39.txt
Writes only q39_source_verification.json next to this script.
"""
from __future__ import annotations
import hashlib
import json
import re
import sys
from pathlib import Path

EXPECTED_BYTES=238528
EXPECTED_LF=3971
EXPECTED_SHA='6712bc969a4cc8c03b15f42bab868148bee9ed68fc39cb9219083e534be7a210'
DEFAULT='PROSHKA_CCM_JOINT_CENTRAL_SOURCE_ROLLBACK_Q39_2026-10-26.txt'
path=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/mnt/data')/DEFAULT
raw=path.read_bytes()
if (len(raw),raw.count(b'\n'),hashlib.sha256(raw).hexdigest())!=(EXPECTED_BYTES,EXPECTED_LF,EXPECTED_SHA):
    raise ValueError('Canonical file mismatch')
raw.decode('utf-8',errors='strict')
pat=re.compile(rb'(?m)^BEGIN_SOURCE (S\d+) ([^\n]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\nBODY:\n')
pos=0
bodies=[]
while True:
    match=pat.search(raw,pos)
    if match is None: break
    sid,name,n,sha=match.groups(); size=int(n)
    body=raw[match.end():match.end()+size]
    if len(body)!=size or hashlib.sha256(body).hexdigest().encode()!=sha:
        raise ValueError('Body mismatch: '+sid.decode())
    stop=match.end()+size
    if not raw[stop:].startswith(b'\nEND_SOURCE'):
        raise ValueError('Separator mismatch: '+sid.decode())
    body.decode('utf-8',errors='strict')
    bodies.append({'id':sid.decode(),'name':name.decode(),'bytes':size,
                   'lf':body.count(b'\n'),'sha256':sha.decode()})
    pos=stop+len(b'\nEND_SOURCE')
if [b['id'] for b in bodies]!=['S'+str(i) for i in range(1,13)]:
    raise ValueError('Expected exactly S1,...,S12')
out={'canonical_bytes':len(raw),'canonical_lf':raw.count(b'\n'),
     'canonical_sha256':EXPECTED_SHA,'canonical_sha_origin':'Measured in this response, not supplied in the user Q39 caption.',
     'body_count':len(bodies),'all_declared_body_hashes_match':True,'bodies':bodies}
Path(__file__).with_name('q39_source_verification.json').write_text(
    json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True))
