#!/usr/bin/env python3
"""Cheap independent assembly/selected-MP checks of saved address cells."""
import ast,csv,hashlib,importlib.util,json,sys,types
from pathlib import Path
import numpy as np
from threadpoolctl import threadpool_limits
P=Path(__file__).resolve().parent;ROOT=P.parent
sys.path[:0]=[str(ROOT/'builder'),'/workspace/conditioning_deps']
from core_components import build
import gmpy2 as g
from flint import acb,arb,ctx

def main():
 rows=list(csv.DictReader((P/'zeta_small_diagonal_controls.csv').open())); checks=[]
 with threadpool_limits(limits=1):
  for m in [75,463,1800]:
   A,meta=build(m,'zeta');diag=np.diag(A['A']);want=np.argsort(diag,kind='stable')[:20];saved=[r for r in rows if int(r['m'])==m];got=np.array([int(r['j'])for r in saved]);assert set(want)==set(got)
   err=max(abs(diag[int(r['j'])]-float(r['zeta_diagonal']))for r in saved);assert err<1e-9
   checks.append(dict(m=m,all20_indices_match=True,max_diagonal_error=err,builder_sha256=hashlib.sha256((ROOT/'builder/core_components.py').read_bytes()).hexdigest()))
 source=ROOT/'inputs/analytic_source.py';spec=importlib.util.spec_from_file_location('_address_check_pinned',source);pinned=importlib.util.module_from_spec(spec);spec.loader.exec_module(pinned)
 tree=ast.parse((P/'inputs/add_dh_dense.py').read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='selected');env=dict(g=g,acb=acb,arb=arb,ctx=ctx,raw=types.SimpleNamespace(exact=types.SimpleNamespace(pinned=pinned)));exec(compile(ast.fix_missing_locations(ast.Module(body=[fn],type_ignores=[])),'frozen_selected_source','exec'),env)
 events=list(csv.DictReader((P/'events.csv').open()));mp=[]
 for m,j in [(75,58),(463,234),(1800,137)]:
  rr=env['selected'](m,[j],320)[0];e=next(r for r in events if int(r['m'])==m and int(r['j'])==j);assert g.mpfr(rr['Ajj'])<0 or g.mpfr(rr['determinant'])<0
  mp.append(dict(selected=rr,event_off_gamma=e['off_gamma'],event_off_distance_steps=e['off_distance_steps'],event_on_gamma=e['on_gamma'],event_on_distance_steps=e['on_distance_steps']))
 out=dict(status='PASS_INDEPENDENT_20_DIAGONAL_CONTROLS_AND_3_SELECTED_MP_EVENTS',zeta_checks=checks,selected_DH_320bit=mp,interval_certificate=False,scope='Fresh full float component assembly for control indices; unchanged selected-entry MP source for three owner example events only. No eigenproblems.')
 (P/'CONTROL_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
