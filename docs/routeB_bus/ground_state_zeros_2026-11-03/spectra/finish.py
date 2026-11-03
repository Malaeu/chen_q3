"""Final coverage and stored-vector checks; never rerun completed source cells."""
import run as r
import subprocess,collections,json,hashlib,time
P=r.P
assert all((r.V/f'{w}_m{m}.json').exists() for m in range(16,301) for w in ['zeta','dh','plant']), 'missing world cells'
rows=[json.loads((r.V/f'{w}_m{m}.json').read_text()) for m in range(16,301) for w in ['zeta','dh','plant']]
checks=[];maxnorm=r.F(0);mindot=r.F(1);minratio=None
for a in rows:
 r.g.get_context().precision=a['source_precision_bits']+80
 m=a['m'];assert a['N']==m
 assert len(a['c'])==m+1 and len(a['v_odd0'])==m
 assert a['c']==a['v_even0']==a['blocks'][0]['v0'] and a['v_odd0']==a['blocks'][1]['v0']
 assert a['ground_resolved'] and a['even_ground_resolved'] and a['odd_ground_resolved'], (m,a['world'],'unresolved')
 for i,(name,n) in enumerate([('even',m+1),('odd',m)]):
  block=a['blocks'][i];high=list(map(r.F,a[f'v_{name}0']));low=list(map(r.F,a[f'v_{name}0_low']))
  assert len(low)==n
  for v,bits in [(high,block['solver_bits_high']),(low,block['solver_bits_low'])]:
   err=abs(sum((x*x for x in v),r.F(0))-1);maxnorm=max(maxnorm,err);assert err<r.F(2)**(-bits+24),(m,a['world'],name,'norm')
  dot=abs(sum((x*y for x,y in zip(high,low)),r.F(0)));mindot=min(mindot,dot);assert dot>r.F('.99999999999999999999'),(m,a['world'],name,'projector replay')
  lo,hi=map(r.F,[block['lambda0'],block['lambda1']]);gap=r.F(block['gap']);scale=max(r.F(1),abs(lo),abs(hi));assert abs(hi-lo-gap)<r.F(2)**(-block['solver_bits_high']+24)*scale
 gap=r.F(a['global_gap']);error=max(r.F(e) for b in a['blocks'] for e in b['eigenvalue_empirical_error']);ratio=gap/error;minratio=ratio if minratio is None else min(minratio,ratio);assert ratio>1000
sourcehashes={k:{a['hashes'][k] for a in rows} for k in ['source_50777d4.py','analytic_source.py']}
assert len(sourcehashes['analytic_source.py'])==1, 'nonuniform analytic source supplier'
pinned_base=(P.parent/'inputs/source_50777d4.py').read_bytes().rstrip(b'\n')
pinned_variants={hashlib.sha256(pinned_base+b'\n'*k).hexdigest():k for k in range(5)}
assert sourcehashes['source_50777d4.py']<=set(pinned_variants), 'pinned source differs beyond documented EOF-newline normalization'
source_normalization={h:dict(terminal_LF_count=pinned_variants[h],canonical_one_LF_sha256=hashlib.sha256(pinned_base+b'\n').hexdigest()) for h in sourcehashes['source_50777d4.py']}
assert hashlib.sha256((P.parent/'inputs/analytic_source.py').read_bytes()).hexdigest() in sourcehashes['analytic_source.py']
producerhashes={a['hashes']['loweig.c'] for a in rows}
assert all((P/'producers'/f'loweig_{h}.c').exists() and hashlib.sha256((P/'producers'/f'loweig_{h}.c').read_bytes()).hexdigest()==h for h in producerhashes)
python_producers={}
for a in rows:
 for key,h in a['hashes'].items():
  if key.endswith('.py') and key not in ['source_50777d4.py','analytic_source.py']:
   python_producers.setdefault(key,set()).add(h)
   matches=list((P/'producers').glob('*_'+h+'.py'))
   assert matches and any(hashlib.sha256(f.read_bytes()).hexdigest()==h for f in matches), (key,h,'missing Python producer archive')
subprocess.run([r.sys.executable,str(P/'summarize.py')],check=True)
subprocess.run([r.sys.executable,str(P/'plot_spectra.py')],check=True)
r.atomic(P/'FINAL_CHECKS.json',dict(status='COMPLETE_855_NUMERICAL_GROUND_CELLS',world_cells=len(rows),integer_m_count=285,worlds=['zeta','dh','plant'],integer_range=[16,300],source_hashes={k:list(v) for k,v in sourcehashes.items()},producer_hashes=sorted(producerhashes),python_producer_hashes={k:sorted(v) for k,v in python_producers.items()},pinned_source_EOF_newline_normalization=source_normalization,max_unit_norm_square_error=str(maxnorm),minimum_absolute_low_high_ground_inner_product=str(mindot),minimum_empirical_global_gap_error_ratio=str(minratio),all_stored_ground_vectors_and_gaps_checked=True,all_cells_resolved=True,certificate=False,checks_scope='coverage, dimensions, source hash uniformity, producer archives, unit norms, projectors, stored gaps, and reported gap/error dominance; no redundant source/eigenvalue rerun'))
print('FINAL COMPLETE',flush=True)
