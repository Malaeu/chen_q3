"""Run reviewed pinned external code under python -I, with explicit trusted deps."""
import sys,runpy,os
from pathlib import Path
deps=os.environ.get('Q1_TRUSTED_DEPS','/workspace/python_deps')
if deps: sys.path.insert(0,deps)
root=os.environ.get('Q1_EXTERNAL_ROOT',str(Path(__file__).resolve().parent/'external_source'))
script=sys.argv[1];sys.argv=[os.path.join(root,script)]+sys.argv[2:]
Path(sys.argv[0]).parent.joinpath('results').mkdir(exist_ok=True)
os.chdir(root)
runpy.run_path(sys.argv[0],run_name='__main__')
