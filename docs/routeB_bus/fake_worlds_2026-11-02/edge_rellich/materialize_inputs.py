#!/usr/bin/env python3
"""Restore the exact pinned inputs from an existing repository; no network."""
from pathlib import Path
import argparse,hashlib,json,subprocess
p=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--repo',required=True,type=Path)
ap.add_argument('--out',required=True,type=Path);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
for r in json.loads((p/'INPUTS.json').read_text())['inputs']:
    b=subprocess.check_output(['git','-C',str(a.repo),'show',r['ref']+':'+r['path']])
    assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']
    target=a.out/r['local_name']
    if target.exists() and target.read_bytes()!=b:
        raise RuntimeError('Refusing to overwrite different input: '+str(target))
    target.write_bytes(b)
print('23 exact pinned input files restored; no network used')
