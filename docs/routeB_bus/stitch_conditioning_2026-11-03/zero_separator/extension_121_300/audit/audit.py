from pathlib import Path
import json,hashlib,csv
from decimal import Decimal as D
P=Path(__file__).resolve().parent;S=Path('/workspace/conditioning_input');z=json.loads((S/'dh_zeros.json').read_text());pairs=z['off_line_pairs'];line=z['critical_line_zeros']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
b=[]
for p in sorted((S/'B_stitch').glob('cell_dh*.json')):
 a=json.loads(p.read_text());q=a['quiet'];T=D(q['T']);nl=sum(D(x['gamma'])<T for x in line);inc=[x for x in pairs if D(x['gamma'])<T];labels=q['zero_constraints'];actual=[x for x in labels if 'complex' in x['kind']];expected=2*nl+4*len(inc)
 missing=[x['gamma'] for x in inc if sum(x['gamma'] in y['z'] for y in actual)!=2]
 b.append(dict(file=p.name,T=str(T),included_quartets=[x['gamma'] for x in inc],line_count=nl,expected_real_rows=expected,saved_real_rows=q['real_constraint_rows'],saved_complex_points=q['complex_evaluation_points'],missing_quartets=missing,pass_counts=expected==q['real_constraint_rows'] and len(actual)==2*len(inc) and not missing))
c=[]
for r in csv.DictReader((S/'C_conditioning/conditioning.csv').open()):
 if r['world']!='dh':continue
 T=D(r['T']);nl=sum(D(x['gamma'])<T for x in line);inc=[x for x in pairs if D(x['gamma'])<T];expected=nl+2*len(inc)
 c.append(dict(m=r['m'],cut=r['cut'],variant=r['variant'],T=str(T),included_quartets=[x['gamma'] for x in inc],expected_real_rows=expected,saved_q=int(r['q']),saved_distinct_heights=int(r['distinct_zero_heights']),expected_distinct_heights=nl+len(inc),pass_counts=expected==int(r['q']) and nl+len(inc)==int(r['distinct_zero_heights'])))
e=dict(status='DIAGNOSTIC_NEVER_A_PROOF',source_ref='3691f8e',table_sha256=sha(S/'dh_zeros.json'),table_bytes=(S/'dh_zeros.json').stat().st_size,table_expected_sha256='e2f5f86d960aff5b45a318723072a1a2c67df3f00b6d213535274831c9afdee1',quartets=pairs,B_source_sha256=sha(P/'B_stitch_stitch.py'),B_source_git_blob='a901d8de8eec3db801e13d00c75125d9269aef32',C_local_source_sha256=sha(S/'C_conditioning/core.py'),B_rows=b,C_rows=c,B_all_pass=all(x['pass_counts'] for x in b),C_all_pass=all(x['pass_counts'] for x in c),C_evidence_limitation='Saved C scalar counts and distinct-height counts checked; per-row labels not persisted in conditioning.csv. Source loops over every table event without filtering quartets beyond strict gamma<T.')
(P/'evidence.json').write_text(json.dumps(e,indent=2)+'\n');print({k:e[k] for k in ['table_sha256','B_source_sha256','C_local_source_sha256','B_all_pass','C_all_pass']});print('B',len(b),'C',len(c),'B maxT',max(float(x['T']) for x in b),'CmaxT',max(float(x['T']) for x in c))
