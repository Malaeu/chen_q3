#!/usr/bin/env python3
"""Replay Q40's new exact controls only; no network or installation.
Usage: python replay_q40.py verdict.md canonical_Q40.txt output_directory
"""
from __future__ import annotations
import hashlib, json, re, subprocess, sys
from pathlib import Path
if len(sys.argv)!=4: raise SystemExit(__doc__)
verdict,canonical,outdir=(Path(x).resolve() for x in sys.argv[1:])
raw=verdict.read_bytes()
pat=re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```(?:python|json)\n',re.M)
assets={};pos=0
while True:
    mat=pat.search(raw,pos)
    if not mat: break
    name,count,digest=mat.groups();name=name.decode();end=mat.end()+int(count)
    body=raw[mat.end():end]
    if name in assets or len(body)!=int(count) or hashlib.sha256(body).hexdigest().encode()!=digest:
        raise ValueError('Asset mismatch: '+name)
    if not raw[end:].startswith(b'```\nEND_ASSET'):
        raise ValueError('Asset fence mismatch: '+name)
    assets[name]=body;pos=end+len(b'```\nEND_ASSET')
expected={'registration_q40.json','check_q40.py','check_q40_results.json',
          'verify_sources_q40.py','q40_source_verification.json','replay_q40.py'}
if set(assets)!=expected: raise ValueError('Unexpected asset list')
outdir.mkdir(parents=True,exist_ok=True)
for name,body in assets.items(): (outdir/name).write_bytes(body)
for script,args in [('check_q40.py',[]),('verify_sources_q40.py',[str(canonical)])]:
    run=subprocess.run([sys.executable,str(outdir/script),*args],cwd=outdir,
                       check=True,capture_output=True,text=True)
    (outdir/(script+'.stdout')).write_text(run.stdout,encoding='utf8')
for name in ('check_q40_results.json','q40_source_verification.json'):
    if (outdir/name).read_bytes()!=assets[name]:
        raise ValueError('Output is not byte-identical: '+name)
print(json.dumps({'assets':len(assets),'asset_hashes_match':True,'checkers_run':2,
                  'both_json_byte_identical':True,'historical_scripts_executed':False},
                 indent=2,sort_keys=True))
