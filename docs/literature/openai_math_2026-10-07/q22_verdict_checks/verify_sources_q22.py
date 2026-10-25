#!/usr/bin/env python3
"""Byte-locked Q22 request verification. Does not certify source theorems."""
import hashlib
import json
import re
import sys
from pathlib import Path

NAME='PROSHKA_CCM_SIGNED_COVARIANCE_ROLLBACK_Q22_2026-10-25.txt'
SIZE=327303
SHA='fa9ec5ceece10bb33fa1be0593c6e2b58da70141ffef954f58e9905aaadaacee'
p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(NAME)
b=p.read_bytes()
assert len(b)==SIZE, (len(b),SIZE)
assert hashlib.sha256(b).hexdigest()==SHA
assert b.endswith(b'\n')
pat=rb'(?m)^(S\d+): (.+?) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$'
rows=[]
for match in re.finditer(pat,b):
    sid,path,n,sha=match.groups(); n=int(n)
    startmarker=b'BEGIN_SOURCE '+sid+b' '+path+b'\n'
    pos=b.index(startmarker)+len(startmarker)
    body=b[pos:pos+n]
    assert hashlib.sha256(body).hexdigest().encode()==sha, sid
    assert b[pos+n:].startswith(b'\nEND_SOURCE '+sid+b'\n'), sid
    rows.append({'id':sid.decode(),'path':path.decode(),'bytes':n,
                 'sha256':sha.decode(),'first_line':b[:pos].count(b'\n')+1,
                 'lf':body.count(b'\n'),'last_line':b[:pos+n].count(b'\n')})
assert len(rows)==11
out={'request':p.name,'bytes':len(b),'lf':b.count(b'\n'),'sha256':SHA,
     'all_eleven_match':True,'sources':rows}
Path(__file__).with_name('source_verification.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'bytes':len(b),'lf':b.count(b'\n'),'sha256':SHA,'sources':len(rows),'status':'BYTE_MATCH'},ensure_ascii=False))
