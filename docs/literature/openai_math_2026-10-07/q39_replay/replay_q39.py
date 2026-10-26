#!/usr/bin/env python3
"""Extract this verdict's six hash-locked assets and replay its two checkers.
Usage: python replay_q39.py verdict.md canonical_Q39.txt ./q39_replay
No downloads, installation, repository changes, or execution of historical assets.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

if len(sys.argv)!=4:
    raise SystemExit(__doc__)
verdict, canonical, outdir = (Path(arg).resolve() for arg in sys.argv[1:])
raw=verdict.read_bytes()
pat=re.compile(rb'(?m)^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```(?:python|json)\n')
pos=0; assets={}
while True:
    match=pat.search(raw,pos)
    if match is None: break
    name_b,count_b,sha_b=match.groups(); name=name_b.decode('ascii')
    if name in assets: raise ValueError('Duplicate asset')
    count=int(count_b); end=match.end()+count
    body=raw[match.end():end]
    if len(body)!=count or hashlib.sha256(body).hexdigest().encode()!=sha_b:
        raise ValueError('Asset mismatch: '+name)
    if not raw[end:].startswith(b'```\nEND_ASSET'):
        raise ValueError('Asset boundary mismatch: '+name)
    assets[name]=body; pos=end+len(b'```\nEND_ASSET')
expected={'registration_q39.json','check_q39.py','check_q39_results.json',
          'verify_sources_q39.py','q39_source_verification.json','replay_q39.py'}
if set(assets)!=expected: raise ValueError('Unexpected asset list')
outdir.mkdir(parents=True,exist_ok=True)
for name,body in assets.items(): (outdir/name).write_bytes(body)
for script,args in [('check_q39.py',[]),('verify_sources_q39.py',[str(canonical)])]:
    run=subprocess.run([sys.executable,str(outdir/script),*args],
                       cwd=outdir,check=True,capture_output=True,text=True)
    (outdir/(script+'.stdout')).write_text(run.stdout,encoding='utf-8')
for name in ['check_q39_results.json','q39_source_verification.json']:
    if (outdir/name).read_bytes()!=assets[name]:
        raise ValueError('Replay output differs: '+name)
print(json.dumps({'asset_count':len(assets),'all_asset_hashes_match':True,
                  'checkers_run':2,'both_json_byte_identical':True,
                  'historical_scripts_run':False},sort_keys=True,indent=2))
