#!/usr/bin/env python3
"""Restore pinned original text inputs using local git objects; no network."""
from pathlib import Path
import argparse,hashlib,json,subprocess
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
for row in json.loads((P/'INPUTS.json').read_text())['inputs']:
    b=subprocess.check_output(['git','-C',str(a.repo),'show',row['ref']+':'+row['path']])
    assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob']
    p=a.out/row['local_name']
    if p.exists() and p.read_bytes()!=b:raise RuntimeError('Conflicting input: '+str(p))
    p.write_bytes(b)
print('Verified pinned original inputs')
