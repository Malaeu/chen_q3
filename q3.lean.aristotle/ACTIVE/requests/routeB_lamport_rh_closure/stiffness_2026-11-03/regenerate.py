"""Authorized fixed calibration only; invoke unchanged pinned builders."""
import os,sys,subprocess,hashlib,json
from pathlib import Path
os.environ['OPENBLAS_NUM_THREADS']='1'
OUT=Path(__file__).resolve().parent;BASE=Path(os.environ['STIFFNESS_BASE']).resolve()
expected=json.loads((OUT/'INPUTS.json').read_text())['files']
for r in expected:
 if r['path'].endswith(('source/split.py','quiet/build.py','source/run.py','quiet/frame.c','quiet/native_frame.py')):
  p=BASE/str(r['path']).split('arithmetic_coupling_2026-11-03/',1)[1];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'],p
subprocess.run([sys.executable,str(BASE/'unpack_data.py')],check=True)
sys.path.insert(0,str(BASE/'source'));import run
for m in [16,24,40,80,120,200,248,300]:run.run(m,True)
subprocess.run([sys.executable,str(BASE/'quiet/build.py'),'--m','16','24','40','80','120','200','248','300'],check=True)
