"""Authoritative scope/correction inventory for immutable raw root diagnostics.
Only existing numerical artifacts are read. No eigenproblem or root search is run.
"""
from pathlib import Path
import json,hashlib,collections,time
import mpmath as mp
P=Path(__file__).resolve().parent;BASE=P.parent;mp.mp.dps=90;start=time.monotonic();expected={(w,m) for w in ['zeta','dh','plant'] for m in range(16,301)};source_cache={};receipts={};stale=[];offaxis=[];cutoff_corrections=[];cells=[];control300=[]
for path in sorted((P/'results').glob('*.json')):
 blob=path.read_bytes();x=json.loads(blob);w=x['world'];m=x['m'];parity=x['parity']
 if w not in ('zeta','dh','plant') or not 16<=m<=300:continue
 raw_source_path=x['source_vector_path'];resolved_source_path=Path(raw_source_path)
 if not resolved_source_path.exists():resolved_source_path=BASE/'spectra/vectors'/resolved_source_path.name
 source_path=str(resolved_source_path)
 if source_path not in source_cache:
  sb=Path(source_path).read_bytes();d=json.loads(sb);block_delta={b['parity']:b['vector_replay_infinity'][0] for b in d.get('blocks',[])};source_cache[source_path]=dict(sha=hashlib.sha256(sb).hexdigest(),world=d['world'],m=d['m'],global_parity=d.get('global_ground_parity'),ground_resolved=d.get('ground_resolved'),even_resolved=d.get('even_ground_resolved'),delta=block_delta)
 src=source_cache[source_path]
 if src['sha']!=x['source_vector_sha256']:stale.append(dict(file=path.name,world=w,m=m,parity=parity));continue
 required=parity=='even' or (src['ground_resolved'] and src['global_parity']==parity);key=f'{w}|{m}|{parity}';receipts[key]=dict(file=path.name,sha256=hashlib.sha256(blob).hexdigest(),source_sha256=src['sha'],required=required,raw_source_path=raw_source_path,resolved_source_path=source_path)
 L=mp.mpf(x['L']);delta=mp.mpf(src['delta'].get(parity,'0'));l2=mp.sqrt(m+1 if parity=='even' else m)*delta;base=mp.sqrt(L)*l2;corrected={};positive_global_nonreal=0;imaginary=0
 for r in x['roots']:
  if not r['kind'].startswith('polynomial'):continue
  re,im=mp.mpf(r['z_re']),mp.mpf(r['z_im']);ay=abs(im);derivative=mp.mpf(r['direct_F_derivative_abs']);factor=mp.sqrt(mp.sinh(ay*L)/(ay*L)) if ay else mp.mpf(1);bound=base*factor;shift=bound/derivative if derivative else mp.inf;corrected[r['root_id']]=shift
  if re>0 and im!=0:positive_global_nonreal+=1
  if re==0 and im!=0:imaginary+=1
  if im!=0:offaxis.append(dict(world=w,m=m,parity=parity,required=required,root_id=r['root_id'],kind=r['kind'],z_re=r['z_re'],z_im=r['z_im'],raw_file=path.name,raw_sha256=receipts[key]['sha256'],source_sha256=src['sha'],real_axis_transform_diagnostic=mp.nstr(base,40),off_axis_growth_factor=mp.nstr(factor,40),corrected_fixed_carrier_transform_diagnostic=mp.nstr(bound,40),corrected_first_order_rootshift_diagnostic=mp.nstr(shift,40),observed_low_high_rootshift=r.get('observed_low_high_root_shift'),scope='Analytically correct complex-plane coefficient-perturbation formula at fixed supplied L, applied to the observed numerical coefficient replay difference. First-order diagnostic, not an exact-source or root-error enclosure.'))
 cutcounts={}
 for cutoff,s in x['cutoffs'].items():
  T=mp.mpf(s['T']);selected=[r for r in x['roots'] if r['kind'].startswith('polynomial') and 0<mp.mpf(r['z_re'])<T and abs(mp.mpf(r['z_im']))<mp.mpf('.5')];nr=sum(mp.mpf(r['z_im'])!=0 for r in selected);mx=max((corrected[r['root_id']] for r in selected),default=None)
  cutoff_corrections.append(dict(world=w,m=m,parity=parity,cutoff=cutoff,required=required,positive_height_nonreal_fourier_count=nr,raw_unscaled_scalar=s.get('max_replay_rootshift_diagnostic'),raw_scalar_valid_real_axis_scope=nr==0,corrected_max_fixed_carrier_first_order_diagnostic=mp.nstr(mx,40) if mx is not None else None))
  cutcounts[cutoff]=nr
 cells.append(dict(world=w,m=m,parity=parity,required=required,full_ground=src['global_parity']==parity,positive_height_nonreal_global_polynomial_count=positive_global_nonreal,pure_imaginary_pairs=imaginary,positive_height_nonreal_strip_counts=cutcounts))
 if m==300:
  s=x['cutoffs']['fixed_c1_4'];control300.append(dict(world=w,parity=parity,full_ground=src['global_parity']==parity,source_count=s['source_count'],source_nonreal_points=s['source_nonreal_count'],source_nonreal_quartets=s['source_nonreal_count']//2,physical_fourier_count=s['fourier_strip_count'],polynomial_fourier_count=s['polynomial_only']['fourier_strip_count'],forced_exterior_count=s['structural_external_count'],fourier_nonreal_strip_points=s['fourier_nonreal_count'],source_recovered_at_1e_6=s['matched_under_1e_6'],source_missing_at_1e_6=s['source_unrecovered_at_1e_6'],max_abs_deviation=s['max_abs_deviation']))
source_keys={(d['world'],d['m']) for d in source_cache.values()};required_keys={f'{w}|{m}|even' for w,m in expected}
for d in source_cache.values():
 if d['ground_resolved'] and d['global_parity']=='odd':required_keys.add(f"{d['world']}|{d['m']}|odd")
missing_required=sorted(required_keys-receipts.keys());summaries={}
for w in ['zeta','dh','plant']:
 primary=[c for c in cells if c['world']==w and c['parity']=='even'];full=[c for c in cells if c['world']==w and c['full_ground']];summaries[w]=dict(primary_even_cells=len(primary),full_ground_cells=len(full),primary_positive_height_nonreal_global_cells=sum(c['positive_height_nonreal_global_polynomial_count']>0 for c in primary),full_ground_positive_height_nonreal_global_cells=sum(c['positive_height_nonreal_global_polynomial_count']>0 for c in full),primary_pure_imaginary_pair_cells=sum(c['pure_imaginary_pairs']>0 for c in primary),full_ground_pure_imaginary_pair_cells=sum(c['pure_imaginary_pairs']>0 for c in full),primary_nonreal_strip_cells={k:sum(c['positive_height_nonreal_strip_counts'][k]>0 for c in primary) for k in ['fixed_c1_4','Omega','0.8Omega']},full_ground_nonreal_strip_cells={k:sum(c['positive_height_nonreal_strip_counts'][k]>0 for c in full) for k in ['fixed_c1_4','Omega','0.8Omega']})
complete=source_keys==expected and not missing_required
out=dict(status='COMPLETE_AUTHORITATIVE_SCOPE_INVENTORY' if complete else 'INCOMPLETE_SCOPE_INVENTORY',seconds=time.monotonic()-start,erratum_sha256=hashlib.sha256((P/'PRECISION_SCOPE_ERRATUM.md').read_bytes()).hexdigest(),formula='B(z)=sqrt(dim)*delta_v_inf*sqrt(sinh(abs(Im(z))*L)/abs(Im(z))); limit sqrt(L)*sqrt(dim)*delta_v_inf on real axis',fixed_carrier_only=True,exact_source_eigenvector_interval_certificate=False,source_cells=len(source_keys),required_root_cells=len(required_keys),current_root_artifacts=len(receipts),missing_required=missing_required,stale=stale,root_receipts=receipts,world_summaries=summaries,control_m300=control300,off_axis_root_diagnostics=offaxis,cutoff_corrected_diagnostics=cutoff_corrections,cells=cells,scope='Authoritative correction to frozen raw off-axis Cauchy diagnostics. Root locations, polynomial certificates, counts and measured precision replays remain unchanged. Empirical numerical source/eigenvector accuracy is not interval certified.')
tmp=P/'PRECISION_SCOPE_INVENTORY.tmp';tmp.write_text(json.dumps(out,indent=2)+'\n');tmp.replace(P/'PRECISION_SCOPE_INVENTORY.json');print(json.dumps(dict(status=out['status'],source_cells=len(source_keys),root_artifacts=len(receipts),off_axis_roots=len(offaxis),world_summaries=summaries)))
