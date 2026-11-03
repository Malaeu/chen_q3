"""Lightweight scheduling checkpoints; full byte/SHA audit remains mandatory.
Cache keys include mtime_ns, size and inode. New/changed atomic source and root
files are read once; immutable files reuse only their small metadata receipts.
"""
from pathlib import Path
import json,hashlib,os
P=Path(__file__).resolve().parent;BASE=P.parent;CACHE=P/'checkpoint_receipts.json'

def load_checkpoint():
 try:old=json.loads(CACHE.read_text())
 except (FileNotFoundError,json.JSONDecodeError):old={}
 sources={};roots={}
 for path in (BASE/'spectra/vectors').glob('*_m*.json'):
  st=path.stat();fingerprint=[st.st_mtime_ns,st.st_size,st.st_ino];key=str(path);entry=old.get('sources',{}).get(key)
  if not entry or entry.get('fingerprint')!=fingerprint:
   blob=path.read_bytes();d=json.loads(blob);entry=dict(path=key,fingerprint=fingerprint,source_sha256=hashlib.sha256(blob).hexdigest(),world=d['world'],m=int(d['m']),global_ground_parity=d.get('global_ground_parity',d.get('global_parity')),ground_resolved=d.get('ground_resolved'),even_ground_resolved=d.get('even_ground_resolved'),odd_ground_resolved=d.get('odd_ground_resolved'),status=d.get('status'))
  sources[key]=entry
 for path in (P/'results').glob('*.json'):
  st=path.stat();fingerprint=[st.st_mtime_ns,st.st_size,st.st_ino];key=str(path);entry=old.get('roots',{}).get(key)
  if not entry or entry.get('fingerprint')!=fingerprint:
   d=json.loads(path.read_text());entry=dict(path=key,fingerprint=fingerprint,world=d['world'],m=int(d['m']),parity=d['parity'],source_vector_sha256=d.get('source_vector_sha256'),census_schema_version=d.get('census_schema_version',0),root_output_digits=d.get('root_output_digits',0),has_replay_floor='spectral_replay_transform_floor' in d.get('checks',{}))
  roots[key]=entry
 out=dict(version=1,sources=sources,roots=roots,scope='Scheduling metadata cache only. Complete final byte/SHA, degree, count and precision-scope audit independently rereads raw artifacts.');tmp=CACHE.with_name(CACHE.name+f'.{os.getpid()}.tmp');tmp.write_text(json.dumps(out)+'\n');tmp.replace(CACHE);return out
