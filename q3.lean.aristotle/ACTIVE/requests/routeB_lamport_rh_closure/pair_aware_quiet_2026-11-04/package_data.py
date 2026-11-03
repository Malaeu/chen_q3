"""Freeze compact receipts; dense matrices/frames remain local."""
from pathlib import Path
import json,hashlib,io,tarfile,gzip,sys,platform,os
from common import P,BASE,MID,HIGH,BUS
LOCAL=Path(os.environ.get('PAIR_LOCAL','/workspace/pair_aware/local'))
# Lossless all300 newcontrol point receipts, no largearrays.
files=sorted(P.glob('control_delta_dh_m*.json'))+sorted(P.glob('control_delta_plant_m*.json'));assert len(files)==300
buf=io.BytesIO();members=[]
with tarfile.open(fileobj=buf,mode='w')as t:
 for f in files:
  raw=f.read_bytes();d=json.loads(raw);labels=d.pop('row_labels');d['row_labels_count']=len(labels);d['row_labels_sha256']=hashlib.sha256(json.dumps(labels,sort_keys=True,separators=(',',':')).encode()).hexdigest();d['row_labels_storage']='LOCAL_REPETITIVE_METADATA; exact input census hashes and q fully specify rows';d['original_full_local_receipt_sha256']=hashlib.sha256(raw).hexdigest();b=(json.dumps(d,indent=2)+'\n').encode();name='control_receipts/'+f.name;info=tarfile.TarInfo(name);info.size=len(b);info.mtime=0;t.addfile(info,io.BytesIO(b));members.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
data=gzip.compress(buf.getvalue(),mtime=0);parts=[]
for i,o in enumerate(range(0,len(data),250000)):
 n=f'control_receipts.tar.gz.part{i:02d}';b=data[o:o+250000];(P/n).write_bytes(b);parts.append(dict(path=n,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
for stale in P.glob('control_receipts.tar.gz.part*'):
 if stale.name not in {r['path']for r in parts}:stale.unlink()
(P/'CONTROL_ARCHIVE.json').write_text(json.dumps(dict(archive_sha256=hashlib.sha256(data).hexdigest(),parts=parts,members=members,scope='all300 scalar/hash receipts; repetitive row labels referenced by input census and row-label hash; original full JSON stays local'),indent=2)+'\n')
# All local NPZ byte hashes; operatorarray contents are intentionally omitted.
rr=[]
for f in sorted(LOCAL.rglob('*.npz')):
 b=f.read_bytes();rr.append(dict(path=str(f.relative_to(LOCAL)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(P/'LOCAL_ARRAY_HASHES.json').write_text(json.dumps(rr,indent=2)+'\n')
paths=[BASE/'METHOD.md',BASE/'separator_summary.csv',BASE/'SCAN_ARCHIVE.json',BASE/'scan_separator.py',BUS/'capacity_matrix_2026-11-02/zeros.csv',BUS/'fake_worlds_2026-11-02/dh_zeros.json']
for packet in[MID,HIGH]:
 paths +=[packet/x for x in ['METHOD.md','RESULT.md','DATA_ARCHIVE.json','SUMMARY.csv','scan_extended.py','native_frame.py','frame.c','zeta_zeros.csv']]
paths+=[MID/'matrix_engine/engine.py',MID/'dh_census/dh_zeros_600_200dps.json',HIGH/'matrix_engine/source.py',HIGH/'matrix_engine/trend.py',HIGH/'dh_census/dh_zeros_900_200dps.json',HIGH/'spike248/REPORT.md',HIGH/'max_delta/MAX_DELTA.csv']
repo=BASE.parents[3];inputs=[]
for f in paths:
 b=f.read_bytes();inputs.append(dict(path=str(f.relative_to(repo)),sha256=hashlib.sha256(b).hexdigest(),git_blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()))
(P/'INPUTS.json').write_text(json.dumps(dict(base='cdb84497649c7399448737732b7dd3d632e141f0',evidence='50777d478c72298ff65c7ffaa2b3783aec183dd6',files=inputs),indent=2)+'\n')
import numpy,scipy,gmpy2,mpmath
(P/'BUILD_INFO.json').write_text(json.dumps(dict(python=sys.version,platform=platform.platform(),numpy=numpy.__version__,scipy=scipy.__version__,gmpy2=gmpy2.version(),mpmath=mpmath.__version__,source='pinned400bit,midGL1928panels; highGL2568panels; same768bitframes',large_arrays_local_only=True,DIAGNOSTIC_NEVER_A_PROOF=True),indent=2)+'\n')
print('Packed300control receipts;',len(data),'archivebytes;',len(rr),'localarrayhashes')
