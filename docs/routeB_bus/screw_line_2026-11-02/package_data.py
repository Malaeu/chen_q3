"""Prepare a compact, lossless commit packet after numerical producers freeze.

Usage: python package_data.py --output /path/to/new/staging-directory
CSV tables and per-cell numeric JSONs remain exact-byte archive members.
"""
from pathlib import Path
import argparse,hashlib,json,re,io,tarfile,gzip

def digest(b):return hashlib.sha256(b).hexdigest()

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    root=Path(__file__).resolve().parent;out=a.output.resolve()
    assert out!=root and root not in out.parents
    out.mkdir(parents=True,exist_ok=True)
    assert not any(out.iterdir()),'Use an empty staging directory'
    archived=[];plain=[]
    for f in sorted(root.rglob('*')):
        if not f.is_file() or '__pycache__' in f.parts or f.suffix in ('.pyc','.log'):continue
        if f.name in ('DATA_MANIFEST.json','SHA256SUMS') or f.name.startswith('data.tar.gz.part'):continue
        rel=f.relative_to(root);name=str(rel)
        data=f.read_bytes()
        cell=(rel.parts[0]=='kernels' and re.fullmatch(r'(zeta|dh)_m[0-9]+_bits[0-9]+\.json',f.name)) or (f.name.startswith('smooth_') and f.suffix=='.json')
        compress=(f.suffix=='.csv' and rel.parts[0]!='source_inputs') or cell or (f.suffix in ('.json','.jsonl') and len(data)>50000)
        (archived if compress else plain).append((name,data))
    buf=io.BytesIO()
    with tarfile.open(fileobj=buf,mode='w',format=tarfile.PAX_FORMAT) as t:
        for name,data in archived:
            info=tarfile.TarInfo(name);info.size=len(data);info.mtime=0;info.mode=0o644
            t.addfile(info,io.BytesIO(data))
    compressed=io.BytesIO()
    with gzip.GzipFile(fileobj=compressed,mode='wb',mtime=0,filename='') as g:g.write(buf.getvalue())
    blob=compressed.getvalue();parts=[]
    for i,start in enumerate(range(0,len(blob),131072)):
        name=f'data.tar.gz.part{i:03d}';data=blob[start:start+131072]
        (out/name).write_bytes(data);parts.append(dict(path=name,sha256=digest(data),bytes=len(data)))
    manifest=dict(status='DIAGNOSTIC_NEVER_A_PROOF',archive_format='concatenated gzip tar; deterministic metadata; exact member bytes',archive_sha256=digest(blob),parts=parts,members=[dict(path=n,sha256=digest(b),bytes=len(b)) for n,b in archived])
    (out/'DATA_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    for name,data in plain:
        f=out/name;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
    files=sorted(f for f in out.rglob('*') if f.is_file())
    (out/'SHA256SUMS').write_text(''.join(digest(f.read_bytes())+'  '+str(f.relative_to(out))+'\n' for f in files))
    print(json.dumps(dict(plain_files=len(plain),archived_members=len(archived),archive_bytes=len(blob),parts=len(parts))))

if __name__=='__main__':main()
