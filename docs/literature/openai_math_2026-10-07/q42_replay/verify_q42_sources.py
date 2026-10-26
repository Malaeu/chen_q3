#!/usr/bin/env python3
"""Byte-framed Q42 intake verification. Never executes historical source code."""
import argparse, hashlib, json, re
from pathlib import Path

HEADER=re.compile(rb'BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n')

def inspect(data, expected):
    data.decode('utf-8',errors='strict')
    sha=hashlib.sha256(data).hexdigest()
    if (len(data),data.count(b'\n'),sha)!=(expected['bytes'],expected['lf'],expected['sha256']):
        raise ValueError('Canonical byte/LF/hash mismatch')
    pos=data.find(b'BEGIN_SOURCE S1 ')
    if pos<0 or (pos and data[pos-1]!=10): raise ValueError('Missing S1')
    rows=[]
    for i,declared in enumerate(expected['sources'],1):
        h=HEADER.match(data,pos)
        if h is None or h[1]!=f'S{i}'.encode(): raise ValueError('Invalid frame order')
        start=h.end(); end=start+int(h[3]); body=data[start:end]
        body.decode('utf-8',errors='strict')
        row={'id':h[1].decode(),'name':h[2].decode(),'bytes':len(body),
             'lf':body.count(b'\n'),'sha256':hashlib.sha256(body).hexdigest(),
             'start_line':data[:start].count(b'\n')+1,'end_line':data[:end].count(b'\n')}
        if row!=declared or row['bytes']!=int(h[3]) or row['lf']!=int(h[4]) or row['sha256']!=h[5].decode():
            raise ValueError(f'Invalid body S{i}')
        suffix=f'\nEND_SOURCE S{i}\n'.encode()
        if data[end:end+len(suffix)]!=suffix: raise ValueError(f'Invalid end S{i}')
        pos=end+len(suffix)
        while pos<len(data) and data[pos:pos+1] in (b'\n',b'\r',b' ',b'\t'): pos+=1
        rows.append(row)
    if pos!=len(data): raise ValueError('Unexpected trailing bytes')
    return {'canonical_file':expected['file'],'canonical_bytes':len(data),'canonical_lf':data.count(b'\n'),
            'canonical_sha256':sha,'source_count':len(rows),'all_body_frames_match':True,
            'historical_code_executed':False,'hashes_certify_mathematics':False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('canonical_txt',type=Path)
    args=p.parse_args(); root=Path(__file__).resolve().parent
    expected=json.loads((root/'q42_source_manifest.json').read_text())
    result=inspect(args.canonical_txt.read_bytes(),expected)
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    (root/'q42_source_verification.json').write_text(text); print(text,end='')

if __name__=='__main__': main()
