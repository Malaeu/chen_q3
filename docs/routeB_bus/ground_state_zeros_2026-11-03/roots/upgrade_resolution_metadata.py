"""Metadata-only upgrade of completed full low/high replays; never recomputes roots."""
from pathlib import Path
import sys,json,hashlib
import mpmath as mp
sys.path.insert(0,str(Path(__file__).resolve().parent));from census import reference_binding
P=Path(__file__).resolve().parent;mp.mp.dps=220
for p in (P/'results').glob('*.json'):
 x=json.loads(p.read_text());rp=x.get('precision_replay',{})
 if x.get('census_schema_version')!=3 or rp.get('status')!='COMPLETE_LOW_HIGH_POLYNOMIAL_ROOT_REPLAY':continue
 src=Path(x['source_vector_path']);blob=src.read_bytes()
 if hashlib.sha256(blob).hexdigest()!=x['source_vector_sha256']:continue
 d=json.loads(blob)
 if not d.get('v_'+x['parity']+'0_low'):continue
 m=x['m'];Om=mp.mpf(x['Omega']);lowOm=2*mp.pi*m/mp.mpf(rp['low_L']);roots={r['root_id']:r for r in x['roots']};mapping={}
 for q in rp['pairs']:
  r=roots[q['root_id']];z=mp.mpc(r['z_re'],r['z_im']);lo=mp.mpc(q['low_z_re'],q['low_z_im']);dist=mp.mpf(q['root_shift']);res=10*(Om**2/max(abs(z),mp.mpf('1e-80'))+lowOm**2/max(abs(lo),mp.mpf('1e-80')))*mp.mpf('1e-165')+mp.mpf('1e-175')*max(1,abs(z),abs(lo))
  q.update(nominal_resolution_allowance=mp.nstr(res,35),root_shift_plus_resolution=mp.nstr(dist+res,40),resolved_above_nominal_floor=bool(dist>res));r['low_high_root_shift_plus_resolution']=q['root_shift_plus_resolution'];mapping[q['root_id']]=q
 for key,cut in x['cutoffs'].items():
  T=mp.mpf(cut['T']);selected=[r for r in x['roots'] if r['kind'].startswith('polynomial') and 0<mp.mpf(r['z_re'])<T and abs(mp.mpf(r['z_im']))<mp.mpf('.5')];shifts=[mp.mpf(mapping[r['root_id']]['root_shift_plus_resolution']) for r in selected]
  old=rp['cutoffs'][key];old['max_observed_root_shift']=old['max_root_shift'];old['max_root_shift']=mp.nstr(max(shifts),40) if shifts else None;old['root_shift_reporting']='Includes conservative nominal allowance from 1e-165 u isolation and 180-digit output; smaller shifts unresolved';old['replay_missing_strip_root_ids']=[];cut['observed_precision_replay']=old
 x['source_reference']=reference_binding(x['world']);x['census_schema_version']=4;x['resolution_metadata_upgrade']='No numerical root recompute; conservative nominal replay-resolution allowance added to previously complete independent low/high isolation';tmp=p.with_suffix('.upgradetmp');tmp.write_text(json.dumps(x,indent=2)+'\n');tmp.replace(p);print(p.name,flush=True)
