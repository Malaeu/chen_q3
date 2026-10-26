#!/usr/bin/env python3
"""Verify the exact canonical Q37 byte frame and all twelve source bodies."""
from pathlib import Path
import argparse, hashlib, json, re
EXPECTED='ac846bc952e69fe19581b927525bbb2648cc8ed4a2b15a608ec1806ab02ca57d'

def verify(path):
    raw=Path(path).read_bytes()
    if (len(raw),raw.count(b'\n'),hashlib.sha256(raw).hexdigest()) != (144454,2231,EXPECTED):
        raise ValueError('Canonical Q37 byte/LF/SHA mismatch')
    raw.decode('utf-8',errors='strict')
    pat=rb'^BEGIN_SOURCE (S\d+) ([^\n]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\nBODY:\n'
    rows=[]
    last=0
    for mt in re.finditer(pat,raw,re.M):
        if mt.start()<last:
            raise ValueError('Overlapping source frames')
        sid,name,size,sha=mt.groups();size=int(size)
        body=raw[mt.end():mt.end()+size]
        if len(body)!=size or hashlib.sha256(body).hexdigest()!=sha.decode():
            raise ValueError('Body hash mismatch: '+sid.decode())
        if not raw[mt.end()+size:].startswith(b'\nEND_SOURCE\n'):
            raise ValueError('Body framing mismatch: '+sid.decode())
        body.decode('utf-8',errors='strict')
        rows.append(dict(id=sid.decode(),name=name.decode(),bytes=size,lf=body.count(b'\n'),
                         sha256=sha.decode(),start_line=raw[:mt.end()].count(b'\n')+1,
                         end_line=raw[:mt.end()+size].count(b'\n')))
        last=mt.end()+size
    if [r['id'] for r in rows]!=['S'+str(i) for i in range(1,13)]:
        raise ValueError('Expected S1 through S12 in order')
    return dict(request_bytes=len(raw),request_lf=raw.count(b'\n'),request_sha256=EXPECTED,
                all_hashes_match=True,source_count=len(rows),sources=rows)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('packet',type=Path)
    ap.add_argument('--output',type=Path,default=Path('q37_sources.json'))
    a=ap.parse_args();out=verify(a.packet)
    a.output.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'source_count':out['source_count'],'all_hashes_match':True}))

if __name__=='__main__':main()
