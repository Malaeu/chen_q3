"""Lossless publication archive; keep all local raw data unchanged."""
from pathlib import Path
import io,tarfile,lzma,json,hashlib
P=Path(__file__).resolve().parent
def selected(f):
    rel=f.relative_to(P)
    if '__pycache__' in rel.parts or f.suffix in ('.pyc','.tmp'): return False
    if f.suffix not in ('.npz','.json','.csv','.log'): return False
    raw=(rel.parts[0]=='C_conditioning' and len(rel.parts)>1 and rel.parts[1] in ('matrices','cells'))
    raw=raw or (rel.parts[0]=='B_stitch' and f.name.startswith(('cell_','partial_')))
    return raw or f.stat().st_size>180000
def main():
    files=sorted(f for f in P.rglob('*') if f.is_file() and selected(f) and f.name!='PUBLICATION_ARCHIVE.json')
    stream=io.BytesIO();members=[]
    with tarfile.open(fileobj=stream,mode='w') as t:
        for f in files:
            b=f.read_bytes();name=str(f.relative_to(P));info=tarfile.TarInfo(name)
            info.size=len(b);info.mtime=0;info.mode=0o644;t.addfile(info,io.BytesIO(b))
            members.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
    data=lzma.compress(stream.getvalue(),preset=6);parts=[]
    for stale in P.glob('data.tar.xz.part*'):stale.unlink()
    for i in range(0,len(data),350000):
        name=f'data.tar.xz.part{i//350000:03d}';b=data[i:i+350000];(P/name).write_bytes(b)
        parts.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
    manifest=dict(format='tar.xz split into ordered parts; lossless',archive_bytes=len(data),archive_sha256=hashlib.sha256(data).hexdigest(),parts=parts,members=members)
    (P/'PUBLICATION_ARCHIVE.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(dict(files=len(files),raw_bytes=sum(x['bytes'] for x in members),compressed_bytes=len(data),parts=len(parts))))
if __name__=='__main__':main()
