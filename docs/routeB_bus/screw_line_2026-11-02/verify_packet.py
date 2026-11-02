"""Check committed bytes and optionally every restored numeric member."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
count=0
for line in (root/'SHA256SUMS').read_text().splitlines():
    wanted,name=line.split('  ',1)
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==wanted,name
    count+=1
manifest=root/'DATA_MANIFEST.json'
restored=0
if manifest.exists():
    for item in json.loads(manifest.read_text())['members']:
        p=root/item['path']
        if p.exists():
            assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],item['path']
            restored+=1
print(f'PASS: {count} committed SHA256 checks; {restored} restored numeric members checked')
