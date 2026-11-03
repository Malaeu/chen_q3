"""Canonical atomic reproducer for the complete m300 LOW bracket artifact.
The three substeps preserve their separate 15/2/3 CPU-second hard caps. The
published artifact remains unchanged if any substep fails or misses a gate.
"""
from pathlib import Path
import os,sys,json,subprocess,hashlib
P=Path(__file__).resolve().parent;target=P/'low_bracket_validation_m300.json';staging=P/f'.low_brackets_reproduce_{os.getpid()}.json';env=dict(os.environ);env['GROUND_ROOT_BRACKET_OUTPUT']=str(staging)
steps=['validate_low_brackets.py','validate_dh_low_imaginary.py','exact_bracket_metadata.py']
try:
 for step in steps:subprocess.run([sys.executable,str(P/step)],env=env,check=True)
 result=json.loads(staging.read_text());assert len(result['rows'])==5
 for row in result['rows']:
  assert row['complete_rounded_low_polynomial_real_root_census'] and row['exact_rational_bracket_disjointness']
  assert row['passed']==row['degree'] and all(q['status']=='PASS' and q['exact_rational_pole_free'] for q in row['checks'])
 result['reproducer']=dict(path=str(Path(__file__).resolve()),sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),steps={s:hashlib.sha256((P/s).read_bytes()).hexdigest() for s in steps},scope='All stages completed in isolated staging; published atomically only after five complete degree/sign/exact-bracket gates pass.')
 staging.write_text(json.dumps(result,indent=2)+'\n');staging.replace(target);print('Published complete m300 LOW bracket artifact atomically')
finally:
 if staging.exists():staging.unlink()
