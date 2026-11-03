"""Lossless archive for large raw data; never removes local raw files."""
from pathlib import Path
import io,tarfile,lzma,json,hashlib
P=Path(__file__).resolve().parent
files=sorted(f for f in P.rglob('*') if f.is_file() and f.suffix in ('.csv','.json') and f.stat().st_size>180000 and '__pycache__' not in f.parts)
raw=io.BytesIO();members=[]
with tarfile.open(fileobj=raw,mode='w') as t:
    for f in files:
        b=f.read_bytes();name=str(f.relative_to(P));info=tarfile.TarInfo(name);info.size=len(b);info.mtime=0;info.mode=0o644;t.addfile(info,io.BytesIO(b))
        members.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
payload=lzma.compress(raw.getvalue(),preset=6);parts=[]
for i in range(0,len(payload),350000):
    name=f'data.tar.xz.part{i//350000:02d}';b=payload[i:i+350000];(P/name).write_bytes(b)
    parts.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
manifest=dict(format='tar.xz split into ordered parts; lossless',archive_bytes=len(payload),archive_sha256=hashlib.sha256(payload).hexdigest(),parts=parts,members=members)
(P/'PUBLICATION_ARCHIVE.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(files=len(files),raw_bytes=sum(x['bytes'] for x in members),compressed_bytes=len(payload),parts=len(parts))))
