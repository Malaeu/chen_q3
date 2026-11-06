# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Bind all top-level delivered files except this self-referential manifest."""
import hashlib,json
from pathlib import Path
H=Path(__file__).resolve().parent
entries=[]
for p in sorted(H.iterdir()):
    if not p.is_file() or p.name=='BLOBS.json':continue
    assert 'checkpoint' not in p.name and not p.name.endswith('.tmp'),p
    data=p.read_bytes()
    entries.append({'path':str(p.relative_to(H.parents[3])),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'git_blob':hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()})
(H/'BLOBS.json').write_text(json.dumps({'excludes':'BLOBS.json itself; temporary Python caches are not deliverables','files':entries},indent=2)+'\n')
print(f'[##############################] 100% ETA 0s {len(entries)} file identities bound')
