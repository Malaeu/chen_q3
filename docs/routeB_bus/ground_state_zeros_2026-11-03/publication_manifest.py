"""Prepare the exact direct-Git publication inventory after lossless packing."""
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
CANON='q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/ground_state_zeros_2026-11-03'
DOCS='docs/routeB_bus/ground_state_zeros_2026-11-03'
def inventory():
    archive=json.loads((P/'PUBLICATION_ARCHIVE.json').read_text())
    # Recheck the actual post-pack raw bytes before omitting them from direct Git.
    for row in archive['members']:
        member=P/row['path'];assert member.is_file() and member.stat().st_size==row['bytes'], row['path']
        h=hashlib.sha256()
        with member.open('rb') as stream:
            while chunk:=stream.read(1048576):h.update(chunk)
        assert h.hexdigest()==row['sha256'], 'Post-pack raw member changed: '+row['path']
    archived={r['path'] for r in archive['members']}
    keep=set(archive['direct_also_published'])
    rows=[];omitted=[]
    for f in sorted(P.rglob('*')):
        if not f.is_file():continue
        rel=str(f.relative_to(P))
        if '__pycache__' in f.parts or f.suffix in ('.pyc','.tmp','.so'):
            continue
        if rel in archived and rel not in keep:continue
        with f.open('rb') as stream:head=stream.read(4)
        if head==b'\x7fELF':
            omitted.append(dict(path=rel,reason='Compiled executable; exact C sources and producer hashes retained'))
            continue
        b=f.read_bytes();rows.append(dict(path=rel,canonical=CANON+'/'+rel,docs=DOCS+'/'+rel,local=str(f),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),git_blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()))
    return rows,omitted

def main():
    assert json.loads((P/'OVERVIEW.json').read_text())['status']=='COMPLETE_FINITE_DIAGNOSTIC'
    rows,omitted=inventory()
    (P/'PUBLICATION_OMISSIONS.json').write_text(json.dumps(dict(binary_omissions=omitted,generated_cache_policy='Python caches and transient .tmp files omitted',raw_scientific_data='All raw archive members retained losslessly; archive manifest enumerates them'),indent=2)+'\n')
    rows,_=inventory()
    (P/'SHA256SUMS').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in rows if r['path']!='SHA256SUMS'))
    rows,_=inventory()
    target=Path('/tmp/ground_publication_manifest.json');target.write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(dict(files=len(rows),direct_bytes=sum(r['bytes'] for r in rows),manifest=str(target))))
if __name__=='__main__':main()
