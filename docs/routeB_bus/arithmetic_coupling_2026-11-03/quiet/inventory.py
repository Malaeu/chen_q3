"""Validate complete quiet-frame inventory and freeze numerical metadata."""
from pathlib import Path
import json,csv,hashlib,numpy as np
P=Path(__file__).resolve().parent

def main():
 rows=[]
 for m in range(16,301):
  for world in ['zeta','dh']:
   name=f'{world}_m{m}';d=json.loads((P/'frames'/f'{name}.json').read_text());f=P/'frames'/f'{name}.npz';data=np.load(f);assert data['Q'].shape==(m+1,d['r']) and data['U'].shape==(m+1,d['q']);assert d['q']+d['r']==m+1;assert max(d['orth_U'],d['orth_Q'],d['cross'])<1e-12
   d['frame_file']=str(f.relative_to(P));d['frame_sha256']=hashlib.sha256(f.read_bytes()).hexdigest();rows.append(d)
 keys=['world','m','q','r','T','method','bits','orth_U','orth_Q','cross','MP_frame_float_orthogonality','smallest_relative_mgs_pivot','quartets_below_T','frame_file','frame_sha256','zero_input_sha256']
 with (P/'INDEX.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=keys,extrasaction='ignore');w.writeheader();w.writerows(rows)
 pilot=[d for d in rows if 'dual_row_projector_difference' in d];summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',cells=len(rows),m_range=[16,300],worlds=['zeta','dh'],double2=dict(frame_world='zeta',label='REFERENCE_Jζ',matching_altered_zero_census=False),max_orth_U=max(d['orth_U'] for d in rows),max_orth_Q=max(d['orth_Q'] for d in rows),max_cross=max(d['cross'] for d in rows),max_MP_frame_float_orthogonality=max(d['MP_frame_float_orthogonality'] for d in rows),pilot_dual_row_projector_max_difference=max(d['dual_row_projector_difference'] for d in pilot),pilot_count=len(pilot),pilot_normalized_E_Q_relative_norm_max=max(d.get('row_normalized_E_Q_relative_norm',0) for d in pilot),source_code_sha256={n:hashlib.sha256((P/n).read_bytes()).hexdigest() for n in ['build.py','native_frame.py','frame.c','inventory.py','pilot_checks.py']},zero_input_sha256={world:next(d['zero_input_sha256'] for d in rows if d['world']==world) for world in ['zeta','dh']},total_frame_bytes=sum((P/d['frame_file']).stat().st_size for d in rows),rank_scope='Distinct-node complete-orbit constraint count; numerical frames, not interval-certified rank.')
 (P/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
