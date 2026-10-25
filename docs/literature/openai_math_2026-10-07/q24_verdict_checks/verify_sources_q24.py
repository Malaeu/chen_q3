"""Verify canonical Q24 and all ten byte-locked bodies; never execute source text."""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parent
name='PROSHKA_CCM_RECIPROCAL_XI_SOURCE_TRANSFER_Q24_2026-10-25.txt'
p=Path(sys.argv[1]) if len(sys.argv)>1 else R/name
b=p.read_bytes(); t=b.decode('utf-8')
assert len(b)==220784 and b.count(b'\n')==2900
assert hashlib.sha256(b).hexdigest()=='be4a92cb75a995b5f3dc3fded8e75990bf5f62ac6dd5b57e7e6f193d7342ba78'
rows=[]
for match in re.finditer(r'^(S\d+): (.+?) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$',t,re.M):
 ident,path,size,sha=match.groups(); size=int(size)
 marker=f'BEGIN_SOURCE {ident} {path}\n'.encode()
 start=b.index(marker)+len(marker); body=b[start:start+size]
 assert len(body)==size and hashlib.sha256(body).hexdigest()==sha
 assert b[start+size:].startswith(f'\nEND_SOURCE {ident}'.encode())
 rows.append({'id':ident,'path':path,'bytes':size,'sha256':sha,'lf':body.count(b'\n')})
assert len(rows)==10
out={'status':'PASS_BYTE_EXACT_Q24_AND_TEN_BODIES','request':name,'bytes':len(b),'lf':b.count(b'\n'),'sha256':hashlib.sha256(b).hexdigest(),'sources':rows}
(R/'source_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
