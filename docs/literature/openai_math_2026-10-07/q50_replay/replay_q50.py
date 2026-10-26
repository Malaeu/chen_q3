#!/usr/bin/env python3
"""Extract Q50 answer assets and replay the standard-library checker.
Usage: python3 replay_q50.py VERDICT.md CANONICAL_Q50.txt [OUTPUT_DIRECTORY]
"""
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,subprocess,sys
HEADER=re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n',re.M)
EXPECTED={'registration_q50.json','check_q50.py','q50_checks.json','replay_q50.py'}

def extract(raw:bytes)->dict[str,bytes]:
    assets={};pos=0
    while True:
        h=HEADER.search(raw,pos)
        if h is None:break
        name=h[1].decode();start=h.end();end=start+int(h[2]);body=raw[start:end]
        if name in assets:raise ValueError('duplicate asset')
        if len(body)!=int(h[2]) or hashlib.sha256(body).hexdigest()!=h[3].decode():
            raise ValueError('asset byte/hash: '+name)
        suffix=b'```\nEND_ASSET\n'
        if raw[end:end+len(suffix)]!=suffix:raise ValueError('asset framing: '+name)
        assets[name]=body;pos=end+len(suffix)
    if set(assets)!=EXPECTED:raise ValueError('asset set')
    return assets

def main():
    if len(sys.argv) not in (3,4):
        raise SystemExit('usage: python3 replay_q50.py VERDICT.md CANONICAL_Q50.txt [OUTPUT_DIRECTORY]')
    verdict=Path(sys.argv[1]).resolve();packet=Path(sys.argv[2]).resolve()
    out=Path(sys.argv[3] if len(sys.argv)==4 else 'q50_replay').resolve()
    a=extract(verdict.read_bytes());out.mkdir(parents=True,exist_ok=True)
    for name,body in a.items():(out/name).write_bytes(body)
    completed=subprocess.run([sys.executable,str(out/'check_q50.py'),str(packet)],cwd=out,capture_output=True,check=True)
    (out/'check_q50.stdout').write_bytes(completed.stdout)
    if (out/'q50_checks.json').read_bytes()!=a['q50_checks.json']:raise ValueError('replay JSON mismatch')
    print(json.dumps(dict(asset_count=len(a),all_hashes_match=True,checker_executed=True,
                         json_byte_identical=True,historical_code_executed=False,
                         production_spectrum=False),sort_keys=True,indent=2))
if __name__=='__main__':main()
