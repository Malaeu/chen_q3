"""Verify the exact Q29 attachment and all nine byte-locked source bodies.
Run: python3 verify_q29_sources.py /path/to/PROSHKA_CCM_ACTUAL_SOURCE_ROLLBACK_Q29_2026-10-26.txt
The argument is the actual local path to the attached canonical TXT.
"""
from pathlib import Path
import hashlib, json, re, sys

EXPECTED=(223966,3385,'652b6f8fd2c4b90eb06101fc8bfa0b85f96062c2ee06a9208fdde71f98d97f2e')
if len(sys.argv)!=2:
    raise SystemExit('Usage: python3 verify_q29_sources.py CANONICAL_Q29_TXT')
p=Path(sys.argv[1]); raw=p.read_bytes(); raw.decode('utf-8')
observed=(len(raw),raw.count(b'\n'),hashlib.sha256(raw).hexdigest())
if observed!=EXPECTED: raise SystemExit('Canonical request mismatch: '+repr(observed))
header=raw.split(b'BEGIN SOURCE S1:',1)[0].decode('utf-8')
rows=re.findall(r'^(S\d+): ([^;\n]+); bytes=(\d+); sha256=([0-9a-f]{64})$',header,re.M)
if len(rows)!=9:raise SystemExit('Expected nine manifest entries')
results=[]
for sid,name,n,sha in rows:
    marker=('BEGIN SOURCE '+sid+': '+name+'\n').encode('utf-8')
    if raw.count(marker)!=1:raise SystemExit('Nonunique source marker: '+sid)
    start=raw.index(marker)+len(marker); n=int(n); body=raw[start:start+n]
    if hashlib.sha256(body).hexdigest()!=sha:raise SystemExit('Source hash mismatch: '+sid)
    if not raw[start+n:].startswith(('\nEND SOURCE '+sid).encode('utf-8')):
        raise SystemExit('Source end/separator mismatch: '+sid)
    body.decode('utf-8')
    results.append({'id':sid,'name':name,'bytes':n,'lf':body.count(b'\n'),'sha256':sha})
out={'status':'PASS_BYTE_LOCKS','request_bytes':observed[0],'request_lf':observed[1],
     'request_sha256':observed[2],'sources':results,
     'scope':'Provenance only. Does not independently verify mathematical source claims.'}
Path(__file__).with_name('source_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
