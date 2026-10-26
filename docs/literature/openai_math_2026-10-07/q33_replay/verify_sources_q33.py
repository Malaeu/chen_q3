#!/usr/bin/env python3
"""Verify exact Q33 bytes and eight declared full source bodies."""
import argparse
import hashlib
import json
from pathlib import Path
import re
EXPECTED='285fe8f99a75e0a858cb5e61e72584efe45181c36f8899489a95238b5bfa3ae0'
def digest(b):return hashlib.sha256(b).hexdigest()
p=argparse.ArgumentParser()
p.add_argument('packet',type=Path)
p.add_argument('--output',type=Path,default=Path('q33_sources.json'))
a=p.parse_args()
raw=a.packet.read_bytes()
if digest(raw)!=EXPECTED:raise SystemExit('Q33 request SHA256 mismatch')
raw.decode('utf-8',errors='strict')
pat=rb'^=== SOURCE (S\d+): (.*?) \| BYTES (\d+) \| SHA256 ([a-f0-9]{64}) ===\n'
entries=[]
for h in re.finditer(pat,raw,re.M):
    sid,name,n,sha=h.groups();n=int(n)
    body=raw[h.end():h.end()+n]
    if len(body)!=n or digest(body)!=sha.decode():
        raise SystemExit('Body mismatch: '+sid.decode())
    ending=b'\n=== END SOURCE '+sid+b' ==='
    if not raw[h.end()+n:].startswith(ending):
        raise SystemExit('Body boundary mismatch: '+sid.decode())
    body.decode('utf-8',errors='strict')
    entries.append({'id':sid.decode(),'name':name.decode(),'bytes':n,
                    'lf':body.count(b'\n'),'sha256':digest(body)})
if [e['id'] for e in entries]!=['S'+str(i) for i in range(1,9)]:
    raise SystemExit('Source ID/count mismatch')
out={'request_bytes':len(raw),'request_lf':raw.count(b'\n'),
     'request_sha256':digest(raw),'source_count':len(entries),'sources':entries}
a.output.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'request_sha256':digest(raw),'source_count':len(entries),'all_hashes_match':True}))
