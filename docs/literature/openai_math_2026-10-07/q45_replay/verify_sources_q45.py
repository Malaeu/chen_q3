#!/usr/bin/env python3
"""Byte-counted verification of the canonical Q45 packet; never executes sources."""
from __future__ import annotations
from pathlib import Path
import hashlib, json, re, sys

EXPECTED_NAME='PROSHKA_CCM_ACTUAL_MOBIUS_FORCING_SEAM_Q45_2026-10-26.txt'
EXPECTED_BYTES=240029
EXPECTED_LF=3714
EXPECTED_SHA='99b3a6c85ca12b6c6eca0371cddab0f2e38507072965659846c683cc98effdf7'
HEADER=re.compile(rb'BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n')

def verify(raw: bytes) -> dict:
    if len(raw)!=EXPECTED_BYTES: raise ValueError('packet byte count')
    if raw.count(b'\n')!=EXPECTED_LF: raise ValueError('packet LF count')
    if hashlib.sha256(raw).hexdigest()!=EXPECTED_SHA: raise ValueError('packet hash')
    raw.decode('utf-8')
    if b'\r' in raw: raise ValueError('unexpected CR')
    if not raw.endswith(b'\n'): raise ValueError('missing final LF')
    if not raw.startswith(b'OPERATIVE_CLASS: TRY_CCM_ACTUAL_MOBIUS_FORCING_SEAM_Q45\n'):
        raise ValueError('request binding')
    entries=[]; pos=0
    for index in range(1,14):
        hit=HEADER.search(raw,pos)
        if hit is None: raise ValueError('missing source header')
        sid,name,bs,lfs,sha=hit.groups()
        if sid!=('S'+str(index)).encode(): raise ValueError('source order')
        start=hit.end(); end=start+int(bs); body=raw[start:end]
        if len(body)!=int(bs) or body.count(b'\n')!=int(lfs): raise ValueError('body length')
        if hashlib.sha256(body).hexdigest()!=sha.decode(): raise ValueError('body hash')
        body.decode('utf-8')
        suffix=b'\nEND_SOURCE '+sid+b'\n'
        if raw[end:end+len(suffix)]!=suffix: raise ValueError('source separator/end')
        entries.append({'id':sid.decode(),'name':name.decode(),'bytes':int(bs),'lf':int(lfs),
                        'sha256':sha.decode(),'start_byte':start,'end_byte':end,
                        'start_line':raw[:start].count(b'\n')+1,
                        'end_line':raw[:end].count(b'\n')})
        pos=end+len(suffix)
    if HEADER.search(raw,pos) is not None: raise ValueError('unexpected extra source')
    if raw[pos:].strip(): raise ValueError('unexpected trailing content')
    return {'packet_name':EXPECTED_NAME,'bytes':len(raw),'lf':raw.count(b'\n'),
            'sha256':hashlib.sha256(raw).hexdigest(),'source_count':len(entries),
            'manifest_verified':True,'historical_code_executed':False,'sources':entries}

if __name__=='__main__':
    if len(sys.argv)!=2: raise SystemExit('usage: python verify_sources_q45.py CANONICAL_Q45.txt')
    raw=Path(sys.argv[1]).read_bytes(); result=verify(raw)
    bad=bytearray(raw); bad[result['sources'][0]['start_byte']+100]^=1
    try: verify(bytes(bad))
    except ValueError: result['single_byte_corruption_detected']=True
    else: raise AssertionError('planted corruption was accepted')
    text=json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q45_source_verification.json').write_text(text,encoding='utf-8')
    print(text,end='')
