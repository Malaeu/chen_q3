"""Restore exact-byte numeric data from the committed split gzip-tar archive."""
from pathlib import Path,PurePosixPath
import hashlib,json,io,tarfile

root=Path(__file__).resolve().parent
manifest=json.loads((root/'DATA_MANIFEST.json').read_text())
data=[]
for part in manifest['parts']:
    value=(root/part['path']).read_bytes()
    assert hashlib.sha256(value).hexdigest()==part['sha256'],part['path']
    data.append(value)
blob=b''.join(data)
assert hashlib.sha256(blob).hexdigest()==manifest['archive_sha256']
expected={x['path']:x for x in manifest['members']}
seen=set()
with tarfile.open(fileobj=io.BytesIO(blob),mode='r:gz') as archive:
    for entry in archive:
        name=PurePosixPath(entry.name)
        assert not name.is_absolute() and '..' not in name.parts
        assert entry.isfile() and entry.name in expected and entry.name not in seen
        seen.add(entry.name)
        content=archive.extractfile(entry).read()
        assert hashlib.sha256(content).hexdigest()==expected[entry.name]['sha256']
        target=root.joinpath(*name.parts);target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(content)
assert seen==set(expected)
print(f"PASS: restored {len(expected)} exact-byte numeric data files")
