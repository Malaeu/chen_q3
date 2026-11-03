"""Final complete-grid receipt, degree, cutoff-count and matching integrity audit.
Reads existing artifacts only; does not recompute source matrices or root searches.
"""
from pathlib import Path
import json,hashlib,collections,sys,time
import mpmath as mp
P=Path(__file__).resolve().parent;BASE=P.parent;mp.mp.dps=90;start=time.monotonic()
expected={(w,m) for w in ['zeta','dh','plant'] for m in range(16,301)};sources={};errors=[];missing=[];methods=collections.Counter();required=[];rows=[];reference_sha={}
for p in (BASE/'spectra/vectors').glob('*_m*.json'):
 blob=p.read_bytes();d=json.loads(blob);key=(d['world'],int(d['m']))
 if key in sources:errors.append(dict(kind='DUPLICATE_SOURCE_KEY',key=key))
 if key not in expected:errors.append(dict(kind='UNEXPECTED_SOURCE_KEY',key=key));continue
 meta={k:d.get(k) for k in ['N','ground_resolved','even_ground_resolved','global_ground_parity','status']}
 meta['coefficient_digests']={par:hashlib.sha256(json.dumps(d['v_even0'] if par=='even' else d['v_odd0'],separators=(',',':')).encode()).hexdigest() for par in ['even','odd']}
 sources[key]=(meta,hashlib.sha256(blob).hexdigest())
for key in sorted(expected-sources.keys()):missing.append(dict(kind='MISSING_SOURCE',world=key[0],m=key[1]))
for (world,m),(d,sha) in sorted(sources.items()):
 if d.get('N')!=m:errors.append(dict(kind='SOURCE_CARRIER_MISMATCH',world=world,m=m))
 if not d.get('even_ground_resolved') or not d.get('ground_resolved'):errors.append(dict(kind='UNRESOLVED_GROUND',world=world,m=m,status=d.get('status')))
 ps=['even']+(['odd'] if d.get('ground_resolved') and d.get('global_ground_parity')=='odd' else [])
 for parity in ps:
  required.append((world,m,parity));p=P/'results'/f'{world}_{parity}_m{m}.json'
  if not p.exists():missing.append(dict(kind='MISSING_ROOT',world=world,m=m,parity=parity));continue
  x=json.loads(p.read_text());tag=dict(world=world,m=m,parity=parity)
  if (x.get('world'),x.get('m'),x.get('parity'))!=(world,m,parity):errors.append(dict(kind='ROOT_IDENTITY',**tag))
  if x.get('global_parity')!=d.get('global_ground_parity'):errors.append(dict(kind='GLOBAL_PARITY_METADATA',**tag))
  if x.get('source_vector_sha256')!=sha:errors.append(dict(kind='STALE_ROOT_SOURCE',**tag));continue
  if not x.get('parity_ground_resolved') or not x.get('ground_resolved'):errors.append(dict(kind='ROOT_GROUND_FLAGS',**tag))
  digest=d['coefficient_digests'][parity]
  if x.get('vector_coefficient_sha256') and x['vector_coefficient_sha256']!=digest:errors.append(dict(kind='COEFFICIENT_DIGEST',**tag))
  if x.get('root_output_digits',0)<180 or x.get('census_schema_version',0)<4:errors.append(dict(kind='LEGACY_ROOT_FORMAT',**tag))
  poly=[r for r in x['roots'] if r['kind'].startswith('polynomial')];degree=x['checks']['degree']
  if len(poly)!=degree or x['checks']['isolated_count']!=degree:errors.append(dict(kind='POLYNOMIAL_DEGREE_ACCOUNTING',**tag))
  ids=[r['root_id'] for r in x['roots']]
  if len(ids)!=len(set(ids)):errors.append(dict(kind='DUPLICATE_ROOT_IDS',**tag))
  L=mp.mpf(x['L']);omega=2*mp.pi/L;method=x['checks'].get('method','Flint complete complex polynomial isolation');methods[method]+=1
  roots={r['root_id']:r for r in x['roots']};cutrows={}
  for cutoff,s in x['cutoffs'].items():
   T=mp.mpf(s['T']);inside=[r for r in x['roots'] if 0<mp.mpf(r['z_re'])<T and abs(mp.mpf(r['z_im']))<mp.mpf('.5')];actual=len(inside);forced=sum(r['kind']=='forced_external' for r in inside)
   # Strict upper endpoint: ceil(T/omega)-1 exterior harmonics lie below T.
   expected_forced=max(0,int(mp.ceil(T/omega))-1-m)
   if cutoff in ('Omega','0.8Omega'):expected_forced=0
   if actual!=s['fourier_strip_count'] or forced!=s['structural_external_count'] or forced!=expected_forced:errors.append(dict(kind='FOURIER_CUTOFF_COUNT',cutoff=cutoff,actual=actual,forced=forced,expected_forced=expected_forced,**tag))
   if actual-forced!=s['polynomial_only']['fourier_strip_count']:errors.append(dict(kind='POLYNOMIAL_CUTOFF_COUNT',cutoff=cutoff,**tag))
   pairs=[q for q in x['matches'] if q['cutoff']==cutoff and q.get('matching_scope','all_fourier')=='all_fourier'];root_ids=[q['root_id'] for q in pairs];source_ids=[str(q['source_index']) for q in pairs]
   if len(root_ids)!=len(set(root_ids)) or len(source_ids)!=len(set(source_ids)):errors.append(dict(kind='NON_ONE_TO_ONE_MATCH',cutoff=cutoff,**tag))
   if any(r not in roots for r in root_ids) or len(pairs)!=min(actual,s['source_count']) or len(pairs)!=s['matched_count']:errors.append(dict(kind='MATCH_CARDINALITY',cutoff=cutoff,**tag))
   near=sum(mp.mpf(q['abs_deviation'])<mp.mpf('1e-6') for q in pairs)
   if near!=s['matched_under_1e_6'] or s['source_unrecovered_at_1e_6']!=s['source_count']-near:errors.append(dict(kind='MATCH_THRESHOLD',cutoff=cutoff,**tag))
   replay=s.get('observed_precision_replay')
   if replay is None:errors.append(dict(kind='MISSING_DIFFERENT_VECTOR_REPLAY',cutoff=cutoff,**tag))
   elif replay.get('replay_missing_strip_root_ids'):errors.append(dict(kind='FAILED_DIFFERENT_VECTOR_REPLAY',cutoff=cutoff,**tag))
   cutrows[cutoff]=dict(source=s['source_count'],physical=actual,polynomial=actual-forced,forced=forced,source_nonreal=s['source_nonreal_count'],fourier_nonreal=s['fourier_nonreal_count'],max_abs_deviation=s['max_abs_deviation'],recovered_at_1e_6=near)
  rows.append(dict(**tag,degree=degree,method=method,polynomial_complex_u=x['checks']['polynomial_nonreal_count'],polynomial_negative_u=x['checks']['polynomial_pure_imaginary_count'],cutoffs=cutrows))
scope_inventory_path=P/'PRECISION_SCOPE_INVENTORY.json'
if scope_inventory_path.exists():
 scope_blob=scope_inventory_path.read_bytes();scope_inventory=json.loads(scope_blob)
 if scope_inventory.get('status')!='COMPLETE_AUTHORITATIVE_SCOPE_INVENTORY' or not scope_inventory.get('fixed_carrier_only') or scope_inventory.get('exact_source_eigenvector_interval_certificate') is not False:errors.append(dict(kind='PRECISION_SCOPE_RECEIPT'))
 for world,m,parity in required:
  key=f'{world}|{m}|{parity}';entry=scope_inventory.get('root_receipts',{}).get(key);path=P/'results'/f'{world}_{parity}_m{m}.json'
  if entry is None or (path.exists() and entry['sha256']!=hashlib.sha256(path.read_bytes()).hexdigest()):errors.append(dict(kind='PRECISION_SCOPE_ROOT_RECEIPT',world=world,m=m,parity=parity))
 scope_receipt=dict(path=str(scope_inventory_path),sha256=hashlib.sha256(scope_blob).hexdigest(),erratum_sha256=hashlib.sha256((P/'PRECISION_SCOPE_ERRATUM.md').read_bytes()).hexdigest())
else:
 errors.append(dict(kind='MISSING_AUTHORITATIVE_PRECISION_SCOPE_INVENTORY'));scope_receipt=None
status='PASS_COMPLETE_GRID' if not errors and not missing and len(sources)==855 else ('INCOMPLETE_GRID' if missing and not errors else 'FAIL_INTEGRITY')
for name in ['zeta_zeros.csv','dh_zeros_900_200dps.json']:reference_sha[name]=hashlib.sha256((BASE/'inputs'/name).read_bytes()).hexdigest()
summary=dict(status=status,seconds=time.monotonic()-start,expected_source_cells=855,source_cells=len(sources),required_root_cells=len(required),audited_root_cells=len(rows),missing=missing,errors=errors,methods=dict(methods),reference_sha256=reference_sha,authoritative_precision_scope=scope_receipt,rows=rows,scope='Complete-grid file/receipt/degree/count/matching/replay integrity audit for existing numerical artifacts. Does not certify source reconstruction, exact eigenvectors, original-source positivity, RH, or any route state.')
tmp=P/'FINAL_AUDIT.tmp';tmp.write_text(json.dumps(summary,indent=2)+'\n');tmp.replace(P/'FINAL_AUDIT.json');print(json.dumps({k:v for k,v in summary.items() if k not in ('rows','missing','errors')}));print('missing',len(missing),'errors',len(errors));sys.exit(0 if status=='PASS_COMPLETE_GRID' else 1)
