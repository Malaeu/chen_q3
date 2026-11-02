"""Lossless archive of raw matched cells; split for transport only."""
from pathlib import Path
import tarfile,hashlib,json
P=Path(__file__).resolve().parent
files=sorted((P/'matched_cells').glob('*.json'))
archive=P/'matched_cells.tar.xz'
with tarfile.open(archive,'w:xz',preset=6) as tar:
 for f in files:tar.add(f,arcname=str(f.relative_to(P)))
b=archive.read_bytes();size=3*1024*1024;parts=[]
for i,start in enumerate(range(0,len(b),size)):
 f=P/f'matched_cells.tar.xz.part{i:02d}';f.write_bytes(b[start:start+size]);parts.append({'file':f.name,'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size})
manifest={'archive_sha256':hashlib.sha256(b).hexdigest(),'archive_bytes':len(b),'parts':parts,'files':{str(f.relative_to(P)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}
(P/'MATCHED_ARCHIVE.json').write_text(json.dumps(manifest,indent=2)+'\n')
with tarfile.open(archive,'r:xz') as tar:
 for name,sha in manifest['files'].items():assert hashlib.sha256(tar.extractfile(name).read()).hexdigest()==sha
archive.unlink()
print(len(files),'files',len(b),'compressed bytes',len(parts),'parts')
