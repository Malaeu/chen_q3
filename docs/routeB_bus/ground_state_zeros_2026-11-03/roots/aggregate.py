"""Deterministic flat tables and precision-qualified descriptive scaling fits."""
from pathlib import Path
import json,csv,math,sys,hashlib,os
import numpy as np
P=Path(__file__).resolve().parent

def write_csv(path,rows):
 if not rows:return
 keys=list(dict.fromkeys(k for r in rows for k in r))
 tmp=path.with_name(path.name+f'.{os.getpid()}.tmp')
 with tmp.open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
 tmp.replace(path)

def main():
 summaries=[];pairs=[];coverage={};replays=[];stale=[];source_hash_cache={};receipts={}
 for p in sorted((P/'results').glob('*.json')):
  x=json.loads(p.read_text());w=x['world'];m=x['m'];par=x['parity']
  if w.startswith('synthetic_'):continue
  source=Path(x['source_vector_path'])
  if not source.exists():source=P.parent/'spectra/vectors'/source.name
  key=str(source)
  if key not in source_hash_cache:source_hash_cache[key]=hashlib.sha256(source.read_bytes()).hexdigest()
  if source_hash_cache[key]!=x['source_vector_sha256']:
   stale.append(dict(world=w,m=m,parity=par,file=str(p),status='STALE_SOURCE_VECTOR_HASH'));continue
  ref=P.parent/'inputs'/('zeta_zeros.csv' if w in ('zeta','plant','planted') else 'dh_zeros_900_200dps.json');binding=dict(path=str(ref),sha256=hashlib.sha256(ref.read_bytes()).hexdigest(),decimal_reference_floor=160 if w in ('zeta','plant','planted') else 200,plant_pair='2*pi/log(2) +/- i/4' if w in ('plant','planted') else None)
  coverage.setdefault(w,{}).setdefault(par,[]).append(m);receipts[f'{w}|{m}|{par}']=x['source_vector_sha256']
  for cut,s in x['cutoffs'].items():
   obs=s.get('observed_precision_replay') or {};ps=s['polynomial_only']
   base=dict(root_method=x['checks'].get('method','Flint complete complex polynomial isolation'),census_producer_sha256=x.get('census_producer_sha256'),isolation_producer_sha256=x['checks'].get('producer_sha256'),continuation_fallback_reason=(x['checks'].get('continuation_fallback') or {}).get('message'),reference_sha256=binding['sha256'],world=w,m=m,parity=par,cutoff=cut,T=s['T'],source_count=s['source_count'],source_nonreal_count=s['source_nonreal_count'],source_nonreal_missing_at_1e_6=s['source_nonreal_count']-sum(float(q['source_im'])!=0 and float(q['abs_deviation'])<1e-6 for q in x.get('matches',[]) if q['cutoff']==cut and q.get('matching_scope','all_fourier')=='all_fourier'),fourier_strip_count=s['fourier_strip_count'],fourier_nonreal_count=s['fourier_nonreal_count'],forced_external_count=s['structural_external_count'],matched_forced_external_count=sum(q['kind']=='forced_external' for q in x.get('matches',[]) if q['cutoff']==cut and q.get('matching_scope','all_fourier')=='all_fourier'),polynomial_strip_count=ps['fourier_strip_count'],polynomial_pure_imaginary_count=x['checks']['polynomial_pure_imaginary_count'],polynomial_nonreal_all_count=x['checks']['polynomial_nonreal_count'],polynomial_nonreal_outside_strip_below_T=s.get('polynomial_nonreal_outside_strip_below_T'),source_count_minus_fourier=s['source_count']-s['fourier_strip_count'],source_count_minus_polynomial=s['source_count']-ps['fourier_strip_count'],max_abs_deviation=s['max_abs_deviation'],max_spacing_scaled_deviation=s['max_spacing_scaled_deviation'],polynomial_only_max_abs_deviation=ps['max_abs_deviation'],matched_under_1e_6=s['matched_under_1e_6'],source_unrecovered_at_1e_6=s['source_unrecovered_at_1e_6'],fourier_unmatched_at_1e_6=s['fourier_unmatched_at_1e_6'],cauchy_replay_rootshift_diagnostic_real_axis_only=s.get('max_replay_rootshift_diagnostic') if s['fourier_nonreal_count']==0 else None,cauchy_scope='fixed-carrier coefficient perturbation on real axis only; authoritative PRECISION_SCOPE_ERRATUM.md',observed_low_high_max_root_shift=obs.get('max_root_shift'),observed_low_high_low_count=obs.get('low_polynomial_strip_count') if x.get('precision_replay',{}).get('low_polynomial',{}).get('certified_low_isolation',False) else None,observed_low_replayed_strip_count=obs.get('low_replayed_strip_root_count',obs.get('low_polynomial_strip_count')),low_replay_count_certified=x.get('precision_replay',{}).get('low_polynomial',{}).get('certified_low_isolation',False),observed_low_high_high_count=obs.get('high_polynomial_strip_count'),replay_missing_strip_root_count=len(obs.get('replay_missing_strip_root_ids',[])),replay_status=x.get('precision_replay',{}).get('status'),vector_precision_dps=x.get('vector_precision_dps',x['source_precision_dps']),matrix_source_precision_dps=x.get('matrix_source_precision_dps'),ground_resolved=x.get('ground_resolved'),parity_ground_resolved=x.get('parity_ground_resolved'),global_parity=x.get('global_parity'),is_full_ground=par==x.get('global_parity'),root_output_digits=x.get('root_output_digits'),census_schema_version=x.get('census_schema_version'),input_sha256=x['source_vector_sha256'])
   summaries.append(base)
  for q in x.get('matches',[]):pairs.append(dict(world=w,m=m,parity=par,**q))
  if x.get('precision_replay',{}).get('status')in ('COMPLETE_LOW_HIGH_POLYNOMIAL_ROOT_REPLAY','ALL_ROOT_NEWTON_LOW_HIGH_REPLAY','PHYSICAL_STRIP_NEWTON_LOW_HIGH_REPLAY','PARTIAL_ROOT_REPLAY_FAILED'):
   for q in x['precision_replay']['pairs']:replays.append(dict(world=w,m=m,parity=par,**q))
 summaries.sort(key=lambda r:(r['world'],r['parity'],r['cutoff'],r['m']))
 write_csv(P/'summary.csv',summaries);write_csv(P/'raw_matches.csv',pairs);write_csv(P/'raw_low_high_replay.csv',replays)
 fits=[]
 for world in sorted(coverage):
  for parity in sorted(coverage[world]):
   for cutoff in ['fixed_c1_4','Omega','0.8Omega']:
    rows=[r for r in summaries if r['world']==world and r['parity']==parity and r['cutoff']==cutoff]
    usable=[];unvalidated=[]
    for r in rows:
     e=float(r['max_abs_deviation']) if r['max_abs_deviation'] is not None else 0
     replay=r.get('observed_low_high_max_root_shift');v=float(replay) if replay is not None else None
     # The 160-digit reference and ~1e-165 isolation set a conservative 1e-155 floor.
     if e<=1e-155:continue
     if v is None or r['replay_missing_strip_root_count']:unvalidated.append(r['m']);continue
     if e>10*v:usable.append((r['m'],e))
    fit=dict(world=world,parity=parity,cutoff=cutoff,available_m=[r['m'] for r in rows],precision_replay_missing_m=unvalidated,precision_qualified_fit_m=[m for m,e in usable],scope='Descriptive fit only. Uses matched maximum distance, excludes values at the 160-digit reference floor, and requires measured different-vector replay < physical deviation/10. Integer-step cutoff changes can produce oscillation; count surplus is separate.')
    if len(usable)>=4:
     xx=np.array([m for m,e in usable],float);yy=np.log10([e for m,e in usable]);a,b=np.polyfit(xx,yy,1);c,d=np.polyfit(np.log10(xx),yy,1)
     models=[]
     for name,coord in [('m',xx),('sqrt_m',np.sqrt(xx)),('m_over_log_m',xx/np.log(xx)),('m_over_log_m_squared',xx/np.log(xx)**2),('log10_m',np.log10(xx))]:
      slope,intercept=np.polyfit(coord,yy,1);res=yy-(slope*coord+intercept);models.append(dict(model=name,slope=float(slope),intercept=float(intercept),rmse_log10=float(np.sqrt(np.mean(res**2)))))
     fit['models']=models
     fit.update(log10_error_vs_m_slope=float(a),log10_error_vs_m_intercept=float(b),log10_error_vs_log10_m_slope=float(c),log10_error_vs_log10_m_intercept=float(d),n=len(usable))
    fits.append(fit)
 desired=set(range(16,301));coverage_out={w:{p:dict(completed_count=len(set(ms)),completed_m=sorted(set(ms)),missing_m=sorted(desired-set(ms))) for p,ms in vv.items()} for w,vv in coverage.items()}
 meta=dict(current_input_receipts=receipts,stale_results=stale,coverage=coverage_out,summary_rows=len(summaries),matching_rows=len(pairs),different_vector_replay_rows=len(replays),scaling=fits,scope='Finite numerical experiment. Complete polynomial census is for decimal vectors; independently rebuilt spectral-precision replay is reported where available. Missing cells remain missing.')
 temp=P/f'aggregate.{os.getpid()}.tmp';temp.write_text(json.dumps(meta,indent=2)+'\n');temp.replace(P/'aggregate.json')
 print(json.dumps(dict(summary_rows=len(summaries),matching_rows=len(pairs),replay_rows=len(replays),coverage={w:{p:len(set(ms)) for p,ms in vv.items()} for w,vv in coverage.items()})))
if __name__=='__main__':main()
