#!/usr/bin/env python3
"""Verify the canonical request and every size-locked embedded source."""
import argparse
import hashlib
import json
import re
from pathlib import Path

EXPECTED_NAME='PROSHKA_CCM_ACTUAL_SIGNED_LOCAL_MOMENTS_Q25_2026-10-25.txt'
EXPECTED_SIZE=291454
EXPECTED_LF=3822
EXPECTED_SHA='d665bc97e8f20f3169b2e3f6c6c21951261779d732fa97f163a002a9055e19e7'

def verify(path:Path):
    raw=path.read_bytes()
    observed={'bytes':len(raw),'LF':raw.count(b'\n'),'sha256':hashlib.sha256(raw).hexdigest(),'final_LF':raw.endswith(b'\n')}
    if (observed['bytes'],observed['LF'],observed['sha256'],observed['final_LF']) != (EXPECTED_SIZE,EXPECTED_LF,EXPECTED_SHA,True):
        raise ValueError(f'Canonical request mismatch: {observed}')
    raw.decode('utf-8',errors='strict')
    header=raw.split(b'BEGIN_SOURCE S1 ',1)[0]
    pattern=rb'(?m)^(S\d+): (.+?) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$'
    rows=[]
    for mat in re.finditer(pattern,header):
        sid,relpath,size,expected=mat.groups(); size=int(size)
        marker=b'BEGIN_SOURCE '+sid+b' '+relpath+b'\n'
        if raw.count(marker)!=1: raise ValueError(f'Nonunique source marker: {sid!r}')
        begin=raw.index(marker)+len(marker); body=raw[begin:begin+size]
        actual=hashlib.sha256(body).hexdigest()
        if actual!=expected.decode(): raise ValueError(f'Source hash mismatch: {sid!r}')
        suffix=raw[begin+size:]
        if not suffix.startswith(b'\nEND_SOURCE '+sid+b'\n'):
            raise ValueError(f'Source separator/end mismatch: {sid!r}')
        body.decode('utf-8',errors='strict')
        rows.append({'id':sid.decode(),'path':relpath.decode(),'bytes':len(body),
                     'sha256':actual,'start_line':raw[:begin].count(b'\n')+1,
                     'end_line':raw[:begin+size].count(b'\n')})
    if len(rows)!=11: raise ValueError(f'Expected 11 sources, got {len(rows)}')
    return {'request':EXPECTED_NAME,'observed':observed,'source_count':11,'sources':rows,
            'scope':'Byte provenance only, not proof verification.'}

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('request',type=Path)
    parser.add_argument('--out',type=Path,default=Path('source_results.json'))
    args=parser.parse_args()
    result=verify(args.request)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Canonical bytes/LF/SHA and 11 full sources: MATCH')
