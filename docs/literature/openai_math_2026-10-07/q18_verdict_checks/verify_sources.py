"""Verify the exact Q18 request and seven embedded source bodies without editing them."""
from pathlib import Path
import re, hashlib, json, sys
ROOT=Path(__file__).resolve().parent
NAME='PROSHKA_CCM_FINITE_DIVISOR_THETA_Q18_2026-10-25.txt'
p=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/NAME
b=p.read_bytes(); text=b.decode('utf-8')
expected='c9ce19cd77a23dfde169e39393f8d2c5ef3046a43c250a71c1dde894cdc963f4'
if len(b)!=169878 or b.count(b'\n')!=2739 or hashlib.sha256(b).hexdigest()!=expected:
    raise ValueError('Q18 request bytes, LF count, or SHA-256 mismatch')
rows=[]
for match in re.finditer(r'^(S\d+): (.+?) \| bytes=(\d+) \| sha256=([0-9a-f]{64})$',text,re.M):
    sid,path,size,sha=match.groups();size=int(size)
    tag=f'===== BEGIN SOURCE {sid}: {path} =====\n'.encode()
    start=b.index(tag)+len(tag); body=b[start:start+size]
    if len(body)!=size or hashlib.sha256(body).hexdigest()!=sha:
        raise ValueError(f'Source mismatch: {sid}')
    if not b[start+size:].startswith(f'\n===== END SOURCE {sid} ====='.encode()):
        raise ValueError(f'Source boundary mismatch: {sid}')
    rows.append({'id':sid,'path':path,'bytes':size,'sha256':sha,'first_raw_line':b[:start].count(b'\n')+1,'last_raw_line':b[:start+size].count(b'\n')})
if len(rows)!=7: raise ValueError('Expected seven complete source bodies')
out={'status':'PASS_BYTE_EXACT_Q18_AND_SEVEN_BODIES','bytes':len(b),'LF':b.count(b'\n'),'sha256':expected,'final_LF':b.endswith(b'\n'),'sources':rows}
(ROOT/'source_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
