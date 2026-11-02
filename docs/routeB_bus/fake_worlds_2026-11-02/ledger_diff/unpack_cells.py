"""Verify and restore the lossless matched_cells archive (Python3.12+)."""
from pathlib import Path
import hashlib,json,io,tarfile
P=Path(__file__).resolve().parent
meta=json.loads((P/'MATCHED_ARCHIVE.json').read_text());chunks=[]
for part in meta['parts']:
 b=(P/part['file']).read_bytes();assert hashlib.sha256(b).hexdigest()==part['sha256'];chunks.append(b)
b=b''.join(chunks);assert hashlib.sha256(b).hexdigest()==meta['archive_sha256']
with tarfile.open(fileobj=io.BytesIO(b),mode='r:xz') as tar:
 assert set(tar.getnames())==set(meta['files'])
 for name,sha in meta['files'].items():
  assert name.startswith('matched_cells/') and '..' not in Path(name).parts
  assert hashlib.sha256(tar.extractfile(name).read()).hexdigest()==sha
 tar.extractall(P,filter='data')
print('Verified and restored',len(meta['files']),'matched cells/source files')
