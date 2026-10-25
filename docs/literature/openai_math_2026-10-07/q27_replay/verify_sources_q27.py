#!/usr/bin/env python3
"""Verify the canonical Q27 byte stream and its nine full source bodies."""
from __future__ import annotations
import hashlib,json,re,sys
from pathlib import Path
name='PROSHKA_CCM_POLYLOG_JOINT_MATRIX_Q27_2026-10-25.txt'
p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(name)
b=p.read_bytes(); b.decode('utf-8',errors='strict')
expected='8c6b5a8e351b2e06efe9846231e9195f72e09709bb4dc0d21e3b8aa40afe46a0'
assert len(b)==198487 and b.count(b'\n')==2641
assert hashlib.sha256(b).hexdigest()==expected
head=b[:b.index(b'BEGIN_SOURCE S1 ')]
rows=re.findall(rb'^(S\d+): (.+?) \| bytes=(\d+) \| sha256=([a-f0-9]{64})$',head,re.M)
assert len(rows)==9
out=[]
for sid,path,size,sha in rows:
    marker=b'BEGIN_SOURCE '+sid+b' '+path+b'\n'
    assert b.count(marker)==1
    start=b.index(marker)+len(marker); n=int(size); body=b[start:start+n]
    assert hashlib.sha256(body).hexdigest().encode()==sha
    assert b[start+n:].startswith(b'\nEND_SOURCE '+sid+b'\n')
    out.append({'id':sid.decode(),'path':path.decode(),'bytes':n,'lf':body.count(b'\n'),'sha256':sha.decode()})
print(json.dumps({'request_bytes':len(b),'request_lf':b.count(b'\n'),'request_sha256':expected,'sources_verified':len(out),'sources':out},ensure_ascii=False,indent=2,sort_keys=True))
