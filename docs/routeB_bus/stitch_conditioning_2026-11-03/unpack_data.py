"""Restore and verify every archived raw file (Python3.12+)."""
from pathlib import Path,PurePosixPath
import json,hashlib,tarfile,io,argparse
P=Path(__file__).resolve().parent
def digest(b):return hashlib.sha256(b).hexdigest()
def main(destination):
    m=json.loads((P/'PUBLICATION_ARCHIVE.json').read_text());chunks=[]
    for q in m['parts']:
        b=(P/q['path']).read_bytes();assert len(b)==q['bytes'] and digest(b)==q['sha256'];chunks.append(b)
    b=b''.join(chunks);assert len(b)==m['archive_bytes'] and digest(b)==m['archive_sha256']
    expected={q['path']:q for q in m['members']};destination=destination.resolve();destination.mkdir(parents=True,exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(b),mode='r:xz') as t:
        entries=t.getmembers();assert len(entries)==len(expected) and {x.name for x in entries}==set(expected)
        for x in entries:
            rel=PurePosixPath(x.name);assert x.isfile() and not rel.is_absolute() and '..' not in rel.parts
            target=(destination/x.name).resolve();assert target.is_relative_to(destination)
            payload=t.extractfile(x).read();q=expected[x.name];assert len(payload)==q['bytes'] and digest(payload)==q['sha256']
            if target.exists():assert target.read_bytes()==payload, f'existing file differs: {target}'
        t.extractall(destination,filter='data')
    for name,q in expected.items():assert digest((destination/name).read_bytes())==q['sha256']
    print(f'Verified and restored {len(expected)} raw files into {destination}')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--destination',type=Path,default=P);args=p.parse_args();main(args.destination)
