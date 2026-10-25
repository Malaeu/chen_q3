#!/usr/bin/env python3
"""Verify the exact Q20 transport and all eleven size-locked source bodies."""
import hashlib, json, re, sys
from pathlib import Path
path = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'PROSHKA_CCM_SOURCE_CONSTRAINT_ROLLBACK_Q20_2026-10-25.txt'
raw=path.read_bytes()
expected='a1464e6a9ea3b49314fa8c704b42904983e45690aa358a772e1dd25bed355276'
assert len(raw)==245193 and raw.count(b'\n')==3554 and raw.endswith(b'\n')
assert hashlib.sha256(raw).hexdigest()==expected
head=raw.split(b'BEGIN_SOURCE S1 ',1)[0].decode('utf-8')
manifest=[]
for sid,source,nb,sha in re.findall(r'^(S\d+): (.*?) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$',head,re.M):
    start_marker=f'BEGIN_SOURCE {sid} {source}\n'.encode()
    pos=raw.index(start_marker)+len(start_marker)
    body=raw[pos:pos+int(nb)]
    assert hashlib.sha256(body).hexdigest()==sha, sid
    assert raw[pos+int(nb):].startswith(f'\nEND_SOURCE {sid}\n'.encode()),sid
    manifest.append({'id':sid,'path':source,'bytes':int(nb),'sha256':sha,
      'line_start':raw[:pos].count(b'\n')+1,
      'line_end':raw[:pos+int(nb)].count(b'\n')})
assert len(manifest)==11
result={'status':'BYTE_AND_HASH_MATCH_NOT_MATHEMATICAL_VERIFICATION','request_bytes':len(raw),
'lf':raw.count(b'\n'),'sha256':expected,'source_count':len(manifest),'sources':manifest}
out=Path(__file__).resolve().parent/'source_verification.json'
out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
