"""Restore the pinned input packet; verify all binary parts before extraction."""
from pathlib import Path
import argparse,urllib.request,json,hashlib,concurrent.futures,tarfile,io
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);P=ap.parse_args().output;P.mkdir(parents=True,exist_ok=True)
base='https://raw.githubusercontent.com/Malaeu/chen_q3/435b7bb94c776851a7133757ba9bf59a2fbc0343/docs/routeB_bus/'
packet=base+'stitch_conditioning_2026-11-03/'
def fetch(url):
 with urllib.request.urlopen(url,timeout=60)as r:return r.read()
raw=fetch(packet+'PUBLICATION_ARCHIVE.json');j=json.loads(raw);(P/'PUBLICATION_ARCHIVE.json').write_bytes(raw)
def part(x):
 d=fetch(packet+x['path']);assert len(d)==x['bytes']and hashlib.sha256(d).hexdigest()==x['sha256'];return d
with concurrent.futures.ThreadPoolExecutor(8)as ex:data=b''.join(ex.map(part,j['parts']))
assert hashlib.sha256(data).hexdigest()==j['archive_sha256']
with tarfile.open(fileobj=io.BytesIO(data))as t:
 for m in t.getmembers():assert m.isfile()and not Path(m.name).is_absolute()and '..'not in Path(m.name).parts
 t.extractall(P,filter='data')
for name,path,digest in [('zeros.csv','capacity_matrix_2026-11-02/zeros.csv','57d2f3da8324551f21c312b5d5ca97a13fca2be61d9039c5da754e04c4a5fecf'),('dh_zeros.json','fake_worlds_2026-11-02/dh_zeros.json','e2f5f86d960aff5b45a318723072a1a2c67df3f00b6d213535274831c9afdee1')]:
 d=fetch(base+path);assert hashlib.sha256(d).hexdigest()==digest;(P/name).write_bytes(d)
print('Restored pinned inputs',P)
