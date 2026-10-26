"""Verify the Q30 canonical packet and all nine byte-locked source bodies.
Usage: python3 verify_sources_q30.py [canonical_TXT_path]
With no argument the TXT is read from the current directory.
"""
from pathlib import Path
import hashlib, json, re, sys

NAME='PROSHKA_CCM_LINKED_HALFGRID_Q30_2026-10-26.txt'
SHA='4846514674d4cd3d5c54103c7c39cab1d7a5e970caf2aa74fae39381838a893a'
p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(NAME)
raw=p.read_bytes()
assert len(raw)==120938 and raw.count(b'\n')==1923
assert hashlib.sha256(raw).hexdigest()==SHA
text=raw.decode('utf-8')
rows=[]
for ident,name,size,digest in re.findall(
        r'^(S\d+): (.*?); bytes=(\d+); sha256=([0-9a-f]{64})$',text,re.M):
    marker=('BEGIN SOURCE '+ident+': '+name+'\n').encode('utf-8')
    start=raw.index(marker)+len(marker)
    body=raw[start:start+int(size)]
    assert hashlib.sha256(body).hexdigest()==digest
    suffix=raw[start+int(size):]
    assert suffix.startswith(('\nEND SOURCE '+ident+'\n').encode('utf-8'))
    rows.append({'id':ident,'name':name,'bytes':len(body),'sha256':digest,
                 'source_start_line':raw[:start].count(b'\n')+1,
                 'source_end_line':raw[:start+len(body)].count(b'\n')})
assert len(rows)==9
out={'status':'PASS_NINE_SOURCE_BODIES',
     'request_bytes':len(raw),'request_lf':raw.count(b'\n'),'request_sha256':SHA,
     'request_hash_status':'OBSERVED_REFERENCE_HASH_NOT_A_USER_SUPPLIED_TOTAL_HASH',
     'source_count':len(rows),'sources':rows,
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('source_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
