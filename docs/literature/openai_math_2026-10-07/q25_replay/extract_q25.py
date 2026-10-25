#!/usr/bin/env python3
"""Extract and hash-check the byte-locked assets from the Q25 Markdown."""
import argparse
import hashlib
import re
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('markdown',type=Path)
parser.add_argument('destination',type=Path)
args=parser.parse_args()
raw=args.markdown.read_bytes()
pattern=rb'<!-- FILE_BEGIN ([A-Za-z0-9_.-]+) bytes=(\d+) sha256=([0-9a-f]{64}) -->\n`````[^\n]*\n'
assets=[]
for match in re.finditer(pattern,raw):
    name,size,expected=match.groups();size=int(size)
    body=raw[match.end():match.end()+size]
    if hashlib.sha256(body).hexdigest()!=expected.decode():
        raise ValueError(f'Asset hash mismatch: {name.decode()}')
    if not raw[match.end()+size:].startswith(b'`````\n<!-- FILE_END '+name+b' -->'):
        raise ValueError(f'Asset end mismatch: {name.decode()}')
    assets.append((name.decode(),body))
if not assets: raise ValueError('No byte-locked assets found')
args.destination.mkdir(parents=True,exist_ok=True)
for name,body in assets:
    (args.destination/name).write_bytes(body)
print(f'Extracted and hash-verified {len(assets)} assets')
