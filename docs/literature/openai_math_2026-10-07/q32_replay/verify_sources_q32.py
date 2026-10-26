#!/usr/bin/env python3
"""Verify canonical Q32 bytes and all seven framed bodies. Standard library only."""
from pathlib import Path
import hashlib,json,re,sys
sha=lambda b:hashlib.sha256(b).hexdigest()
p=Path(sys.argv[1] if len(sys.argv)>1 else 'PROSHKA_CCM_SIGNED_NEAR_FREQUENCY_Q32_2026-10-26.txt')
b=p.read_bytes()
assert sha(b)=='cb93c4eca7007eed3dc559c78996a6b3a0c3db3adaff86bc8e0c52eee2bd1b8f'
assert len(b)==126527 and b.count(b'\n')==2227 and b.endswith(b'\n')
b.decode('utf-8')
pat=rb'^=== SOURCE (S\d+): (.*?) \| BYTES (\d+) \| SHA256 ([0-9a-f]{64}) ===\n'
records=[]; last=0
for z in re.finditer(pat,b,re.M):
    sid,name,n,h=z.groups(); n=int(n)
    assert z.start()>=last
    body=b[z.end():z.end()+n]
    assert len(body)==n and sha(body)==h.decode();body.decode('utf-8')
    end=b'\n=== END SOURCE '+sid+b' ==='
    assert b[z.end()+n:z.end()+n+len(end)]==end
    records.append(dict(id=sid.decode(),name=name.decode(),bytes=n,lf=body.count(b'\n'),sha256=h.decode(),start_line=b[:z.end()].count(b'\n')+1,verified=True))
    last=z.end()+n+len(end)
assert [r['id'] for r in records]==[f'S{i}' for i in range(1,8)]
res={'request':{'bytes':len(b),'lf':b.count(b'\n'),'sha256':sha(b),'verified':True},'sources':records,'source_count':7}
Path(sys.argv[2] if len(sys.argv)>2 else 'source_results.json').write_text(json.dumps(res,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
print(json.dumps({'request_verified':True,'sources_verified':len(records)}))
