#!/usr/bin/env python3
"""Byte-exact Q40 intake verification; no historical script execution.
Usage: python verify_sources_q40.py /path/to/canonical_Q40.txt
"""
from __future__ import annotations
import hashlib, json, re, sys
from pathlib import Path

NAME='PROSHKA_CCM_SIGNED_BLOCK_COUPLING_Q40_2026-10-26.txt'
EXPECTED_BYTES=129772
EXPECTED_LF=2209
EXPECTED_SHA='771ae3b7ce9b657227cc939bfb2d922658b5985a258ea5ef6241d14865c8987c'
p=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/mnt/data')/NAME
raw=p.read_bytes(); sha=hashlib.sha256(raw).hexdigest()
if (len(raw),raw.count(b'\n'),sha)!=(EXPECTED_BYTES,EXPECTED_LF,EXPECTED_SHA):
    raise ValueError('Canonical Q40 mismatch')
raw.decode('utf8',errors='strict')
pat=re.compile(rb'^BEGIN_SOURCE (S\d+) ([^\n]+?) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n',re.M)
rows=[];pos=0
for i in range(1,11):
    match=pat.search(raw,pos)
    if not match or match.group(1)!=f'S{i}'.encode():
        raise ValueError('Source sequence mismatch')
    sid,name,n,lf,digest=match.groups();start=match.end();stop=start+int(n)
    body=raw[start:stop];body.decode('utf8',errors='strict')
    if (len(body),body.count(b'\n'),hashlib.sha256(body).hexdigest().encode())!=(int(n),int(lf),digest):
        raise ValueError('Body mismatch: '+sid.decode())
    end=f'\nEND_SOURCE S{i}\n'.encode()
    if raw[stop:stop+len(end)]!=end:
        raise ValueError('Size-locked boundary mismatch')
    rows.append({'id':sid.decode(),'name':name.decode(),'bytes':int(n),'lf':int(lf),
                 'sha256':digest.decode(),'first_body_line':raw[:start].count(b'\n')+1,
                 'last_body_line':raw[:stop].count(b'\n')})
    pos=stop+len(end)
if raw[pos:].strip(): raise ValueError('Unexpected trailing content')
out={'canonical_file':NAME,'canonical_bytes':len(raw),'canonical_lf':raw.count(b'\n'),
     'canonical_sha256':sha,'whole_file_hash_origin':'Measured here; Q40 caption did not specify a whole-file hash.',
     'all_declared_bytes_lf_sha256_match':True,'strict_source_boundaries_match':True,
     'body_count':len(rows),'sources':rows,'historical_scripts_executed':False}
text=json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True)+'\n'
Path(__file__).with_name('q40_source_verification.json').write_text(text,encoding='utf8')
print(text,end='')
