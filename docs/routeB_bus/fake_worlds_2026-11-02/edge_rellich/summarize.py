"""Aggregate the requested saved cells and explicit source-balance tails."""
from pathlib import Path
import csv,json,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=100
cells=[json.loads(p.read_text()) for p in sorted((P/'cells').glob('*_o192.json'))]
cells.sort(key=lambda d:(d['world']!='zeta',d['m'],d['q']))
assert len(cells)==21, len(cells)
assert sum(d['world']=='zeta' for d in cells)==8
rows=[];zr=[]
for d in cells:
    f=d['finite'];w=d['physical_weak'];z=d['zero_blocks']
    rows.append({'world':d['world'],'m':d['m'],'q':d['q'],'mode':d['mode'],
                 'T':d['T'],'lambda':d['lambda'],'f_b':d['f_b'],'fprime_b_exact':0,
                 'finite_volume':f['volume'],'finite_boundary_subtracted':f['boundary_subtracted'],
                 'finite_commutator':f['commutator'],
                 'finite_boundary_over_lambda':f['boundary_vs_lambda']['ratio_to_lambda'],
                 'finite_boundary_10pct_pass':f['boundary_vs_lambda']['passes_10pct'],
                 'negative_finite_boundary_10pct_pass':f['negative_boundary_vs_lambda']['passes_10pct'],
                 'weak_volume':w['volume'],'weak_boundary':w['boundary'],'weak_total':w['total'],
                 'weak_boundary_over_lambda':d['weak_boundary_vs_lambda']['ratio_to_lambda'],
                 'weak_boundary_10pct_pass':d['weak_boundary_vs_lambda']['passes_10pct'],
                 'projection_return':d['projection_return_weak_minus_finite_volume'],
                 'alternative_commutator':d['alternative_generator']['commutator'],
                 'source_Rayleigh_relative_error':d['lambda_relative_replay_error']})
    for quantity in ['energy','commutator','finite_volume','finite_boundary','weak_total']:
        zr.append({'world':d['world'],'m':d['m'],'q':d['q'],'mode':d['mode'],'quantity':quantity,
                   'head_le_T':z['head'][quantity], 'prefix_T_to_census':z['prefix'][quantity],
                   'source_balance_above_T':z['source_balance_'+quantity+'_above_T'],
                   'source_balance_beyond_census':z['source_balance_'+quantity+'_beyond_census'],
                   'census_cutoff':z['census_cutoff'],
                   'tail_scope':'UNCOMPUTED_SOURCE_BALANCE_NOT_INDEPENDENT_ZERO_TAIL'})
for name,data in [('summary.csv',rows),('zero_sides.csv',zr)]:
    with (P/name).open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=data[0]);wr.writeheader();wr.writerows(data)
refinements=[]
for p in sorted((P/'cells').glob('*_o256.json')):
    hi=json.loads(p.read_text());lo=json.loads(p.with_name(p.name.replace('_o256','_o192')).read_text())
    a={'input':hi['input'],'low_dps':lo['dps'],'high_dps':hi['dps'],'low_order':192,'high_order':256}
    for key,x,y in [('lambda',lo['lambda'],hi['lambda']),
                    ('commutator',lo['finite']['commutator'],hi['finite']['commutator']),
                    ('finite_boundary',lo['finite']['boundary_subtracted'],hi['finite']['boundary_subtracted']),
                    ('weak_total',lo['physical_weak']['total'],hi['physical_weak']['total']),
                    ('weak_boundary',lo['physical_weak']['boundary'],hi['physical_weak']['boundary'])]:
        x,y=mp.mpf(x),mp.mpf(y);a[key+'_absolute_difference']=mp.nstr(abs(x-y),80)
        a[key+'_relative_difference']=mp.nstr(abs(x-y)/max(abs(y),mp.mpf('1e-100')),80)
    refinements.append(a)
assert len(refinements)==3, len(refinements)
validation={'status':'DIAGNOSTIC_NEVER_A_PROOF','baseline_cells':21,'zeta_cells':8,'dh_cells':13,
            'max_source_Rayleigh_relative_error':mp.nstr(max(mp.mpf(d['lambda_relative_replay_error']) for d in cells),80),
            'identity_max_absolute_errors':{k:mp.nstr(max(mp.mpf(d['validation'][k]) for d in cells),80) for k in cells[0]['validation']},
            'fixed_vector_refinements':refinements,'interval_certification':False,'new_eigenproblems':0}
assert mp.mpf(validation['max_source_Rayleigh_relative_error'])<mp.mpf('1e-60')
assert max(mp.mpf(x) for x in validation['identity_max_absolute_errors'].values())<mp.mpf('1e-85')
assert max(mp.mpf(v) for r in refinements for k,v in r.items() if k.endswith('_relative_difference'))<mp.mpf('1e-50')
(P/'VALIDATION.json').write_text(json.dumps(validation,indent=2)+'\n')
def short(x):return mp.nstr(mp.mpf(x),10)
table=['|world|m|q|lambda|C=[A,D]|Bfinite/lambda|Bweak/lambda|',
       '|---|---:|---:|---:|---:|---:|---:|']
for r in rows:
    table.append('|'+ '|'.join([r['world'],str(r['m']),str(r['q']),short(r['lambda']),short(r['finite_commutator']),short(r['finite_boundary_over_lambda']),short(r['weak_boundary_over_lambda'])])+'|')
(P/'TABLE.md').write_text('\n'.join(table)+'\n')
print(json.dumps({'cells':21,'zeta_boundary_passes':sum(r['finite_boundary_10pct_pass'] for r in rows if r['world']=='zeta'),
                  'zeta_weak_boundary_passes':sum(r['weak_boundary_10pct_pass'] for r in rows if r['world']=='zeta'),
                  'validation':validation},indent=2))
