#!/usr/bin/env python3
"""Extract Q45's new assets by exact byte lengths and replay the two checkers.
Usage: python replay_q45.py VERDICT.md CANONICAL_Q45.txt [OUTPUT_DIRECTORY]
The canonical packet and its historical programs are never executed.
"""
from __future__ import annotations
from pathlib import Path
import hashlib, json, re, subprocess, sys

HEAD=re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n',re.M)
EXPECTED={'check_q45.py','check_q45_results.json','verify_sources_q45.py',
          'q45_source_verification.json','registration_q45.json','replay_q45.py'}

def main():
    if len(sys.argv) not in (3,4):
        raise SystemExit('usage: python replay_q45.py VERDICT.md CANONICAL_Q45.txt [OUTPUT_DIRECTORY]')
    verdict=Path(sys.argv[1]).resolve(); canonical=Path(sys.argv[2]).resolve()
    out=Path(sys.argv[3] if len(sys.argv)==4 else 'q45_replay').resolve()
    raw=verdict.read_bytes(); pos=0; assets={}
    while True:
        hit=HEAD.search(raw,pos)
        if hit is None: break
        name=hit[1].decode(); size=int(hit[2]); start=hit.end(); end=start+size
        body=raw[start:end]
        if name in assets: raise ValueError('duplicate asset '+name)
        if len(body)!=size or hashlib.sha256(body).hexdigest()!=hit[3].decode():
            raise ValueError('asset bytes/hash '+name)
        suffix=b'```\nEND_ASSET\n'
        if raw[end:end+len(suffix)]!=suffix: raise ValueError('asset framing '+name)
        assets[name]=body; pos=end+len(suffix)
    if set(assets)!=EXPECTED: raise ValueError('asset set mismatch')
    out.mkdir(parents=True,exist_ok=True)
    for name,body in assets.items(): (out/name).write_bytes(body)
    for script,args in [('check_q45.py',[]),('verify_sources_q45.py',[str(canonical)])]:
        proc=subprocess.run([sys.executable,str(out/script),*args],cwd=out,
                            capture_output=True,text=True,check=True)
        (out/(script+'.stdout')).write_text(proc.stdout,encoding='utf-8')
    for name in ('check_q45_results.json','q45_source_verification.json'):
        if (out/name).read_bytes()!=assets[name]: raise ValueError('output mismatch '+name)
    answer={'asset_count':len(assets),'all_asset_hashes_match':True,
            'checkers_run':2,'both_json_byte_identical':True,
            'historical_scripts_run':False,'production_spectrum_run':False}
    print(json.dumps(answer,sort_keys=True,indent=2))

if __name__=='__main__': main()
