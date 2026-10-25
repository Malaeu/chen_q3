#!/usr/bin/env python3
"""Verify Q21 bytes and the eleven source bodies, without editing them."""
from pathlib import Path
import hashlib, json, re, sys
HERE=Path(__file__).resolve().parent
p=Path(sys.argv[1]) if len(sys.argv)>1 else HERE.parent/'PROSHKA_CCM_CONTACT_AWARE_JOINT_ENERGY_Q21_2026-10-25.txt'
b=p.read_bytes()
sha='f1bf29b823d4d5a8f61d3f510c46231fdb29bb9bd0d1cace2c5958266e61ffde'
assert len(b)==171850 and b.count(b'\n')==2571 and b.endswith(b'\n')
assert hashlib.sha256(b).hexdigest()==sha
head=b.split(b'BEGIN_SOURCE S1 ',1)[0].decode('utf-8')
rows=[]
for sid,path,size,digest in re.findall(r'^(S\d+): (.*?) \| bytes=(\d+) \| sha256=([a-f0-9]{64})$',head,re.M):
    marker=f'BEGIN_SOURCE {sid} {path}\n'.encode()
    start=b.index(marker)+len(marker)
    body=b[start:start+int(size)]
    assert hashlib.sha256(body).hexdigest()==digest,sid
    assert b[start+int(size):].startswith(f'\nEND_SOURCE {sid}\n'.encode()),sid
    rows.append({'id':sid,'path':path,'bytes':len(body),'sha256':digest,
                 'line_start':b[:start].count(b'\n')+1,
                 'line_end':b[:start+int(size)].count(b'\n')})
assert len(rows)==11
out={'status':'EXACT_BYTES_AND_HASHES_NOT_PROOF_VALIDATION','request_bytes':len(b),'request_lf':b.count(b'\n'),
     'request_sha256':sha,'hash_origin':'computed from the mounted canonical request; individual body hashes matched the supplied manifest',
     'source_count':len(rows),'sources':rows}
(HERE/'source_verification.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
