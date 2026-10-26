#!/usr/bin/env python3
"""Validate the canonical Q35 bytes and all eleven complete source bodies."""
from pathlib import Path
import argparse, hashlib, json, re

EXPECTED = 'bb9c58db7abe7f2f77e156b94473c0ac93fe7808fbd931f16ebbc4686d620a56'

def verify(path):
    raw=Path(path).read_bytes()
    digest=hashlib.sha256(raw).hexdigest()
    if len(raw)!=158021 or raw.count(b'\n')!=2685 or digest!=EXPECTED:
        raise ValueError('Canonical packet byte count, LF count, or SHA256 mismatch')
    raw.decode('utf-8', errors='strict')
    pat=rb'^BEGIN_SOURCE (S\d+) ([^\n]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\nBODY:\n'
    records=[]
    for mt in re.finditer(pat,raw,re.M):
        sid,name,size,sha=mt.groups(); size=int(size)
        body=raw[mt.end():mt.end()+size]
        got=hashlib.sha256(body).hexdigest()
        if len(body)!=size or got!=sha.decode() or not raw[mt.end()+size:].startswith(b'\nEND_SOURCE\n'):
            raise ValueError('Body mismatch: '+sid.decode())
        body.decode('utf-8', errors='strict')
        records.append({'id':sid.decode(),'name':name.decode(),'bytes':size,
                        'lf':body.count(b'\n'),'sha256':got,
                        'body_start_line':raw[:mt.end()].count(b'\n')+1,
                        'body_end_line':raw[:mt.end()+size].count(b'\n')})
    if [r['id'] for r in records] != ['S'+str(i) for i in range(1,12)]:
        raise ValueError('Expected exactly S1 through S11')
    return {'request_bytes':len(raw),'request_lf':raw.count(b'\n'),'request_sha256':digest,
            'source_count':len(records),'all_hashes_match':True,'sources':records}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('packet',type=Path)
    ap.add_argument('--output',type=Path,default=Path('q35_sources.json'))
    a=ap.parse_args(); obj=verify(a.packet)
    a.output.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'source_count':obj['source_count'],'all_hashes_match':True}))

if __name__=='__main__':
    main()
