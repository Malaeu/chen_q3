"""MP confirmation on EXACT saved binary frame columns; no reframing.
Existing p5 cell files are not edited. Source400bits/GL2568panels/MP120dps.
"""
from pathlib import Path
import json,csv,pickle,hashlib,time
import numpy as np
import mpmath as mp
from p5 import Kernels,ROOT,OUT,LOCAL,serial,sha
mp.mp.dps=120
rows=[];cells=[]
for m in (16,24,40):
 t0=time.monotonic();framepath=ROOT/'quiet/frames'/f'zeta_m{m}.npz';saved=np.load(framepath)['Q']
 # mp.mpf(Python float) exactly lifts its binary64 value, rather than
 # roundtripping through a shortened decimal string or refitting its span.
 Q=mp.matrix([[mp.mpf(float(v))for v in row]for row in saved])
 cache=(LOCAL/'mp')/f'm{m}.pkl'
 with cache.open('rb')as f:z=pickle.load(f)
 A=z['A'];K=Kernels(m,prec='mp');base=K.convert(K.base);gate=max(abs(x)for x in base-A)
 if gate>mp.mpf('1e-110'):raise ArithmeticError('source reconstruction failed')
 H=K.convert(K.curvature());HC=Q.T*H*Q;diag=[HC[j,j]for j in range(HC.rows)];positive=[j for j,v in enumerate(diag)if v>0];negative=[j for j,v in enumerate(diag)if v<0]
 Qpoly=z['Q'];projected=Qpoly*(Qpoly.T*Q);projection_differences=[];projected_curvatures=[]
 for j in range(Q.cols):
  v=projected[:,j];v/=mp.norm(v);projection_differences.append(mp.norm(v-Q[:,j]));projected_curvatures.append(mp.fdot(v,H*v))
 for j,h in enumerate(diag):rows.append(dict(m=m,frame_file=str(framepath.relative_to(ROOT)),frame_sha256=sha(framepath),column_index_zero_based=j,column_name=f'saved_Q_column_{j:03d}',h_mp=mp.nstr(h,115),projected_h_mp=mp.nstr(projected_curvatures[j],115),normalized_projection_difference_mp=mp.nstr(projection_differences[j],115),sign='positive'if h>0 else('negative'if h<0 else'zero'),basis_origin='owner-authorized regenerated quiet/frames binary64 Q exact-lifted unchanged into MP120dps; original archived NPZ byte identity not established'))
 cells.append(dict(m=m,source_gate_maxentry=gate,source_gate_tolerance=mp.mpf('1e-110'),frame_sha256=sha(framepath),columns=HC.rows,all_saved_frame_columns_negative=not positive and len(negative)==HC.rows,positive_columns_zero_based=positive,positive_values=[diag[j]for j in positive],projected_positive_values=[projected_curvatures[j]for j in positive],maximum_normalized_projection_difference=max(projection_differences),projected_positive_columns_zero_based=[j for j,v in enumerate(projected_curvatures)if v>0],minimum_diagonal=min(diag),maximum_diagonal=max(diag),orthogonality_defect=mp.norm(Q.T*Q-mp.eye(Q.cols)),cache_polynomial_basis_all_negative=json.loads((OUT/f'p5_mp_m{m}.json').read_text())['quiet_basis_all_negative'],scope='saved binary frame directions tested unchanged; not orthogonalized or replaced by cache polynomial basis',seconds=time.monotonic()-t0))
 print('S4 savedframe MP',m,'positive',positive,mp.nstr(max(diag),20),flush=True)
with(OUT/'p5_S4_FRAME_CONFIRMATION.csv').open('w',newline='')as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
(OUT/'p5_S4_FRAME_CONFIRMATION.json').write_text(json.dumps(serial(dict(status='DIAGNOSTIC_NEVER_A_PROOF',precision='source400bits_GL2568panels_mp120dps',source_floor='empirical ~1e-114, not interval enclosure',saved_frames_S4_all_pilots_pass=all(c['all_saved_frame_columns_negative']for c in cells),cells=cells,existing_p5_cell_files_edited=False,frame_provenance='owner-authorized unchanged-builder regeneration; original archived NPZ hashes not matched; no original-byte score asserted')),indent=2)+'\n')
