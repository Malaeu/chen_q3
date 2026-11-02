"""Restore exact large diagnostic data from checked lossless archive (Python3.12+)."""
from pathlib import Path
import io,tarfile,json,hashlib
P=Path(__file__).resolve().parent
meta=json.loads((P/'PUBLICATION_ARCHIVE.json').read_text());chunks=[]
for part in meta['parts']:
    b=(P/part['file']).read_bytes()
    assert hashlib.sha256(b).hexdigest()==part['sha256']
    chunks.append(b)
b=b''.join(chunks);assert hashlib.sha256(b).hexdigest()==meta['archive_sha256']
with tarfile.open(fileobj=io.BytesIO(b),mode='r:xz') as tar:
    assert set(tar.getnames())==set(meta['files'])
    for name,sha in meta['files'].items():
        path=Path(name)
        assert not path.is_absolute() and '..' not in path.parts
        assert hashlib.sha256(tar.extractfile(name).read()).hexdigest()==sha
        old=P/name
        if old.exists():assert hashlib.sha256(old.read_bytes()).hexdigest()==sha
    tar.extractall(P,filter='data')
print('Verified and restored',len(meta['files']),'diagnostic files')
