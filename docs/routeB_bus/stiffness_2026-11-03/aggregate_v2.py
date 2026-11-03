from pathlib import Path
import json,csv,hashlib,io,tarfile,gzip,sys,os
import numpy as np,scipy.linalg as la
P=Path(__file__).resolve().parent
BASE=Path(os.environ.get('STIFFNESS_BASE','/workspace/stiffness/repo/docs/routeB_bus/arithmetic_coupling_2026-11-03'));LOCAL=Path(os.environ.get('STIFFNESS_LOCAL',str(P.parent/'local')))
def csvwrite(name,rows):
 keys=list(dict.fromkeys(k for row in rows for k in row))
 with(P/name).open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
rows=[];gates=[];spectra=[];inertias=[];intervals=[];prices=[];overlaps=[]
for f in sorted((P/'binary_cells').glob('*.json')):
 d=json.loads(f.read_text());p2=d.get('P2',{});p3=d.get('P3',{});rows.append(dict(world=d['world'],m=d['m'],precision='binary64_calibration',epsilon=d['epsilon'],source_gate=d['P1_gate'],face_size=d['face_size'],gap_ratio=d['face_gap_ratio'],face_gate=d['face_gate'],face_relative=d['face_relative'],price_kernel_at_source_floor=p2.get('kernel_dimension'),price_kernel_at_face_tolerance=p2.get('face_tolerance_kernel_dimension'),primal_lower_bound=p3.get('primal_value'),dual_upper_envelope=p3.get('dual_upper_envelope'),status=p3.get('status','STOPPED_FACE_GATE')))
 gates.append({k:d[k]for k in ['world','m','source_reconstruction_max_entry','rho','P1_gate','face_size','face_PAP_norm','face_component_norm_max','face_relative','face_gate','face_sum_residual']})
 for k,s in enumerate(p2.get('singular_values',[])):spectra.append(dict(world=d['world'],m=d['m'],index=k,singular_value=s,source_threshold=p2['threshold'],face_threshold=p2['face_tolerance_threshold']))
 for knob,i in d['inertias'].items():inertias.append(dict(world=d['world'],m=d['m'],knob=knob,**i))
 for x in d['P4']:intervals.append(dict(world=d['world'],m=d['m'],epsilon=d['epsilon'],**x))
 for x in d['exit_overlaps']:overlaps.append(dict(world=d['world'],m=d['m'],precision='binary',face_size=d['face_size'],**x))
 if 't'in p3:
  for label,t in zip(d['labels'],p3['t']):prices.append(dict(world=d['world'],m=d['m'],knob=label,soft_candidate_t=t,candidate_minimum=p3['primal_minimum'],candidate_status=p3['status']))
for m in [16,24,40]:
 d=json.loads((P/f'mp_prices_m{m}.json').read_text());f=d['literal_face'];b=f['P3_ball'];rows.append(dict(world='zeta',m=m,precision='MP120_source400_GL256',epsilon='1e-100',source_gate=d['P1_gate_pass'],face_size=d['selected_face_size'],gap_ratio=d['selected_gap_ratio'],face_gate=f['gate_pass'],face_relative=f['compression_relative'],price_kernel_at_source_floor=f['P2_full_map']['kernel_dimension'],price_kernel_at_face_tolerance='',primal_lower_bound=b['scalar_analytic_ball_optimum'],status='RESOLVED_SCALAR_SOFT_DIRECTION'))
csvwrite('SUMMARY.csv',rows);csvwrite('P1_GATES.csv',gates);csvwrite('P2_SINGULAR_VALUES.csv',spectra);csvwrite('P3_BINARY_CANDIDATES.csv',prices);csvwrite('P4_INERTIAS.csv',inertias);csvwrite('P4_INTERVALS.csv',intervals);csvwrite('FACE_EXIT_OVERLAPS.csv',overlaps)
# Record exact regenerated artifacts and semantic array payloads; arrays stay local.
original={(x['world'],int(x['m'])):x for x in csv.DictReader((BASE/'quiet/INDEX.csv').open())};hashes=[]
for sub in ['source','quiet/frames']:
 for m in [16,24,40,80,120,200,248,300]:
  for w in (['zeta','dh','double2']if sub=='source'else['zeta','dh']):
   f=BASE/sub/f'{w}_m{m}.npz';b=f.read_bytes();z=np.load(f);arrays={key:dict(shape=list(z[key].shape),dtype=str(z[key].dtype),sha256=hashlib.sha256(z[key].tobytes(order='C')).hexdigest())for key in z.files};r=dict(path=str(f.relative_to(BASE)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),arrays=arrays)
   if sub!='source':
    old=original[w,m];Q=z['Q'];U=z['U'];r.update(original_npz_sha256=old['frame_sha256'],exact_file_hash_match=old['frame_sha256']==r['sha256'],q=U.shape[1],r=Q.shape[1],Q_orth=float(la.norm(Q.T@Q-np.eye(Q.shape[1]),2)),U_orth=float(la.norm(U.T@U-np.eye(U.shape[1]),2)),cross=float(la.norm(Q.T@U,2)))
   hashes.append(r)
for m in [16,24,40]:
 f=LOCAL/'mp'/f'm{m}.pkl';hashes.append(dict(path=f'local/mp/m{m}.pkl',sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size,scope='LOCAL_ONLY_PICKLE_CACHE; portable scientific values in scalar receipts'))
(P/'REGENERATED_ARRAYS.json').write_text(json.dumps(hashes,indent=2)+'\n')
# Dense dual stress candidates remain local. Publish scalar/eigen/vector receipts.
members=[];buf=io.BytesIO()
with tarfile.open(fileobj=buf,mode='w')as t:
 for file in sorted((P/'binary_cells').glob('*.json')):
  d=json.loads(file.read_text())
  if 'P3'in d:
   Y=d['P3'].pop('dual_Y',None)
   if Y is not None:d['P3']['dual_Y_local_sha256']=hashlib.sha256(np.array(Y,dtype='<f8').tobytes()).hexdigest();d['P3']['dual_Y_storage']='LOCAL_ONLY_DENSE_ARRAY'
  data=(json.dumps(d,indent=2)+'\n').encode();name='binary_receipts/'+file.name;info=tarfile.TarInfo(name);info.size=len(data);info.mtime=0;t.addfile(info,io.BytesIO(data));members.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
blob=gzip.compress(buf.getvalue(),mtime=0);parts=[]
for i,o in enumerate(range(0,len(blob),250000)):
 name=f'binary_receipts.tar.gz.part{i:02d}';b=blob[o:o+250000];(P/name).write_bytes(b);parts.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(P/'BINARY_ARCHIVE.json').write_text(json.dumps(dict(sha256=hashlib.sha256(blob).hexdigest(),members=members,parts=parts),indent=2)+'\n');print('27summary rows,24binary receipts,43local array hashes; dense arrays excluded')
