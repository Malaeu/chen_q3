"""Verify the unchanged Q17 packet and its seven size-locked source bodies."""
from pathlib import Path
import re,hashlib,json,sys
R=Path(__file__).resolve().parent
name='PROSHKA_CCM_ZERO_SELECTIVE_PAIR_Q17_2026-10-25.txt'
p=Path(sys.argv[1]) if len(sys.argv)>1 else R/name
b=p.read_bytes();text=b.decode('utf-8')
assert len(b)==126407 and b.count(b'\n')==1919
assert hashlib.sha256(b).hexdigest()=='b26a7672a0aeb4049f4e42e157014a4c318f788ed299d52f0ee728623de51245'
rows=[]
for m in re.finditer(r'^(S\d+): (.+?) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$',text,re.M):
 ident,path,size,sha=m.groups()
 tag=f'===== BEGIN SOURCE {ident}: {path} =====\n'.encode()
 start=b.index(tag)+len(tag);body=b[start:start+int(size)]
 assert len(body)==int(size) and hashlib.sha256(body).hexdigest()==sha
 assert b[start+int(size):].startswith(b'\n===== END SOURCE '+ident.encode()+b' =====')
 rows.append({'id':ident,'path':path,'bytes':int(size),'sha256':sha,
              'first_raw_line':b[:start].count(b'\n')+1,
              'last_raw_line':b[:start+int(size)].count(b'\n')})
assert len(rows)==7
out={'status':'PASS_BYTE_EXACT_PACKET_AND_SEVEN_BODIES',
     'request':name,'bytes':len(b),'lf':b.count(b'\n'),
     'sha256':hashlib.sha256(b).hexdigest(),'source_count':len(rows),'sources':rows}
(R/'source_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
