#!/usr/bin/env python3
"""Verify and restore lossless native cells; refuse conflicting existing files."""
from pathlib import Path
import argparse,gzip,hashlib,json,re
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
manifest=json.loads((P/'NATIVE_ARCHIVE.json').read_text());chunks=[]
for part in manifest['parts']:
    b=(P/part['name']).read_bytes()
    assert len(b)==part['bytes'] and hashlib.sha256(b).hexdigest()==part['sha256']
    chunks.append(b)
b=b''.join(chunks);assert hashlib.sha256(b).hexdigest()==manifest['sha256']
raw=gzip.decompress(b);assert hashlib.sha256(raw).hexdigest()==manifest['uncompressed_sha256']
expected={x['name']:x for x in manifest['cells']};seen=set();a.out.mkdir(parents=True,exist_ok=True)
for line in raw.splitlines():
    d=json.loads(line);name=d['name'];assert name in expected and name not in seen
    assert re.fullmatch(r'(zeta|dh)_m\d+_dps\d+_gl\d+(_nodeplus|_nodeminus)?\.json',name)
    seen.add(name);data=d['content'].encode('utf-8');rec=expected[name]
    assert len(data)==rec['bytes'] and hashlib.sha256(data).hexdigest()==rec['sha256']
    path=a.out/name
    if path.exists() and path.read_bytes()!=data:raise RuntimeError('Conflicting file: '+str(path))
    path.write_bytes(data)
assert seen==set(expected)
print('Verified and restored',len(seen),'native numeric cells')
