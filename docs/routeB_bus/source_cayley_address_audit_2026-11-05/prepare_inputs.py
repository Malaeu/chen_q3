"""Materialize only the pinned read-only Git inputs for a replay workspace."""
from pathlib import Path
import subprocess,json,hashlib,os
P=Path(__file__).resolve().parent;repo=Path(os.environ.get('CCM_REPO','/workspace/stiffness/repo'))
for item in json.loads((P/'INPUTS.json').read_text())['inputs']:
 if 'local_input'not in item:continue
 b=subprocess.check_output(['git','show',item['ref']+':'+item['path']],cwd=repo)
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==item['git_blob']
 assert hashlib.sha256(b).hexdigest()==item['sha256']
 (P.parent/item['local_input']).write_bytes(b)
print('Pinned raw inputs materialized and verified; no matrix builder executed')
