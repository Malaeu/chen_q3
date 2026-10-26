#!/usr/bin/env python3
"""Extract and replay Q47's four new assets; never execute historical sources.
Usage: python3 replay_q47.py VERDICT.md CANONICAL_Q47.txt [OUTPUT_DIRECTORY]
"""
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,subprocess,sys
HEAD=re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n',re.M)
EXPECTED={'registration_q47.json','check_q47.py','q47_checks.json','replay_q47.py'}
def extract(raw):
    assets={};pos=0
    while True:
        h=HEAD.search(raw,pos)
        if h is None: break
        name=h[1].decode();start=h.end();end=start+int(h[2]);body=raw[start:end]
        if name in assets: raise ValueError('duplicate asset')
        if len(body)!=int(h[2]) or hashlib.sha256(body).hexdigest()!=h[3].decode():
            raise ValueError('asset length/hash '+name)
        suffix=b'```\nEND_ASSET\n'
        if raw[end:end+len(suffix)]!=suffix: raise ValueError('asset frame '+name)
        assets[name]=body;pos=end+len(suffix)
    if set(assets)!=EXPECTED: raise ValueError('asset set')
    return assets

def main():
    if len(sys.argv) not in (3,4):
        raise SystemExit('usage: python3 replay_q47.py VERDICT.md CANONICAL_Q47.txt [OUTPUT_DIRECTORY]')
    verdict=Path(sys.argv[1]).resolve();canonical=Path(sys.argv[2]).resolve()
    out=Path(sys.argv[3] if len(sys.argv)==4 else 'q47_replay').resolve()
    a=extract(verdict.read_bytes());out.mkdir(parents=True,exist_ok=True)
    for name,body in a.items(): (out/name).write_bytes(body)
    run=subprocess.run([sys.executable,str(out/'check_q47.py'),str(canonical)],
                       cwd=out,capture_output=True,text=True,check=True)
    (out/'check_q47.stdout').write_text(run.stdout,encoding='utf-8')
    if (out/'q47_checks.json').read_bytes()!=a['q47_checks.json']:
        raise ValueError('checker JSON differs')
    print(json.dumps(dict(asset_count=len(a),all_hashes_match=True,checker_run=True,
                         json_byte_identical=True,historical_programs_executed=False,
                         production_spectrum_run=False),sort_keys=True,indent=2))
if __name__=='__main__':main()
