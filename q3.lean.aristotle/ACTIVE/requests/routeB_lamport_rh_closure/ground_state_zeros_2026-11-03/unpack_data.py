"""Restore raw scientific data with streaming decompression and SHA256 checks."""
from pathlib import Path,PurePosixPath
import json,hashlib,tarfile,lzma,tempfile,argparse,shutil
P=Path(__file__).resolve().parent
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(1048576):h.update(b)
    return h.hexdigest()
def main(destination):
    m=json.loads((P/'PUBLICATION_ARCHIVE.json').read_text());destination=destination.resolve();destination.mkdir(parents=True,exist_ok=True)
    expected={r['path']:r for r in m['members']};seen=set();h=hashlib.sha256();total=0
    with tempfile.TemporaryDirectory(prefix='ground_restore_') as tmp:
        archive=Path(tmp)/'data.tar.xz'
        with archive.open('wb') as out:
            for part in m['parts']:
                f=P/part['path'];assert f.stat().st_size==part['bytes'] and sha(f)==part['sha256']
                with f.open('rb') as src:
                    while b:=src.read(1048576):h.update(b);total+=len(b);out.write(b)
        assert total==m['archive_bytes'] and h.hexdigest()==m['archive_sha256']
        with lzma.open(archive,'rb') as dec:
            with tarfile.open(fileobj=dec,mode='r|') as t:
                for item in t:
                    name=item.name;rel=PurePosixPath(name);assert item.isfile() and not rel.is_absolute() and '..' not in rel.parts
                    assert name in expected and name not in seen;seen.add(name);r=expected[name];assert item.size==r['bytes']
                    target=(destination/name).resolve();assert target.is_relative_to(destination);target.parent.mkdir(parents=True,exist_ok=True)
                    if target.exists():
                        assert target.stat().st_size==r['bytes'] and sha(target)==r['sha256'],f'Existing file differs: {target}'
                        # Consume and verify the archived copy too.
                        stream=t.extractfile(item);hh=hashlib.sha256()
                        while b:=stream.read(1048576):hh.update(b)
                        assert hh.hexdigest()==r['sha256']
                    else:
                        tmpfile=target.with_name(target.name+'.restore.tmp');stream=t.extractfile(item);hh=hashlib.sha256();size=0
                        with tmpfile.open('wb') as out:
                            while b:=stream.read(1048576):out.write(b);hh.update(b);size+=len(b)
                        assert size==r['bytes'] and hh.hexdigest()==r['sha256'];tmpfile.replace(target)
        assert seen==set(expected)
    print(f'Verified and restored {len(seen)} raw files into {destination}')
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--destination',type=Path,default=P);a=ap.parse_args();main(a.destination)
