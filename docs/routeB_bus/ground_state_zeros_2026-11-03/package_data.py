"""Stream a lossless raw-data archive after all producers have frozen."""
from pathlib import Path
import tarfile,hashlib,json,io,tempfile,subprocess
P=Path(__file__).resolve().parent
DIRECT_KEEP={'NEAREST_SOURCE.csv','CONTROL_SCALING.csv','GAPS.csv','ZERO_SUMMARY.csv','SCALING.csv','SCALING_EDGE.csv','BOUNDARY_ROOTS.csv','CARRIER_CONTROL.csv','spectra/vectors/zeta_m300.json'}
def selected(f):
    r=f.relative_to(P);name=str(r)
    if '__pycache__' in r.parts or f.suffix in ('.pyc','.tmp') or f.name=='PUBLICATION_ARCHIVE.json':return False
    if f.suffix not in ('.json','.csv','.npz','.log','.stdout','.stderr'):return False
    core=len(r.parts)>1 and r.parts[:2] in [('spectra','vectors'),('roots','results')]
    return core or (name not in DIRECT_KEEP and f.stat().st_size>220000)
def main():
    assert json.loads((P/'OVERVIEW.json').read_text())['status']=='COMPLETE_FINITE_DIAGNOSTIC'
    files=sorted(f for f in P.rglob('*') if f.is_file() and selected(f))
    fd=tempfile.TemporaryDirectory(prefix='ground_archive_');archive=Path(fd.name)/'data.tar.xz';members=[]
    # Four fast 8MiB dictionaries keep packaging CPU/memory bounded.
    command=['xz','-T4','--lzma2=preset=1,dict=8MiB','--check=crc64','-c']
    with archive.open('wb') as compressed, subprocess.Popen(command,stdin=subprocess.PIPE,stdout=compressed) as encoder:
        with tarfile.open(fileobj=encoder.stdin,mode='w|') as t:
            for f in files:
                b=f.read_bytes();name=str(f.relative_to(P));info=tarfile.TarInfo(name);info.size=len(b);info.mtime=0;info.mode=0o644;info.uid=info.gid=0;info.uname=info.gname=''
                t.addfile(info,io.BytesIO(b));members.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
        encoder.stdin.close();assert encoder.wait()==0, 'xz encoder failed'
    for f in P.glob('data.tar.xz.part*'):f.unlink()
    parts=[];total=0;digest=hashlib.sha256()
    with archive.open('rb') as f:
        while b:=f.read(1500000):
            name=f'data.tar.xz.part{len(parts):03d}';(P/name).write_bytes(b);digest.update(b);total+=len(b);parts.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
    out=dict(format='Streaming tar.xz, ordered1.5MB parts; lossless raw files',compression_command=command,compression_version=subprocess.run(['xz','--version'],capture_output=True,text=True,check=True).stdout.splitlines()[0],archive_bytes=total,archive_sha256=digest.hexdigest(),parts=parts,members=members,direct_also_published=['spectra/vectors/zeta_m300.json'])
    (P/'PUBLICATION_ARCHIVE.json').write_text(json.dumps(out,indent=2)+'\n');fd.cleanup();print(json.dumps(dict(members=len(members),raw_bytes=sum(x['bytes'] for x in members),compressed_bytes=total,parts=len(parts))))
if __name__=='__main__':main()
