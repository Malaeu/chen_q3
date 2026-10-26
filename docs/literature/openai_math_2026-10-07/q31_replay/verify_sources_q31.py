#!/usr/bin/env python3
"""Verify the exact canonical Q31 request and its seven byte-framed bodies."""
from __future__ import annotations
import hashlib,json,re,sys
from pathlib import Path

EXPECTED='f2dd26aa178b15847da95532e15c57f9caa719618ac2fa56da20abacac930ba7'
def digest(data:bytes)->str:return hashlib.sha256(data).hexdigest()
request=Path(sys.argv[1] if len(sys.argv)>1 else 'PROSHKA_CCM_ACTUAL_IMAGE_DEFICIT_Q31_2026-10-26.txt')
output=Path(sys.argv[2] if len(sys.argv)>2 else 'source_results.json')
raw=request.read_bytes()
assert digest(raw)==EXPECTED, 'canonical request SHA256 mismatch'
assert len(raw)==107988 and raw.count(b'\n')==1801
raw.decode('utf-8')
pattern=re.compile(rb'^=== SOURCE (S\d+): (.*?) \| BYTES (\d+) \| SHA256 ([0-9a-f]{64}) ===\n',re.M)
records=[]
last_end=0
for match in pattern.finditer(raw):
    source_id,name,size,expected=match.groups(); size=int(size)
    assert match.start()>=last_end, 'nested/overlapping source framing'
    begin=match.end(); end=begin+size
    body=raw[begin:end]
    assert len(body)==size and digest(body)==expected.decode(), source_id
    body.decode('utf-8')
    marker=b'\n=== END SOURCE '+source_id+b' ==='
    assert raw[end:end+len(marker)]==marker, 'bad separator/end marker'
    records.append({'id':source_id.decode(),'name':name.decode(),'bytes':size,
                    'lf':body.count(b'\n'),'sha256':digest(body),'verified':True})
    last_end=end+len(marker)
assert [r['id'] for r in records]==[f'S{i}' for i in range(1,8)]
result={'request':{'bytes':len(raw),'lf':raw.count(b'\n'),'sha256':digest(raw),'verified':True},
        'source_count':len(records),'sources':records}
output.write_text(json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps({'request_verified':True,'source_count':len(records),'output':str(output)}))
