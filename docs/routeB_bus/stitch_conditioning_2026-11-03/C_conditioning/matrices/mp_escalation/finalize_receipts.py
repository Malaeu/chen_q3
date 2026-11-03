"""Metadata/hash closeout only; no eigenproblem or source recomputation."""
from pathlib import Path
import json,hashlib,collections,csv,re
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=100
files=sorted(P.glob('mp_cell_*.json'));seen=set();rows=[];methods=collections.Counter()
for f in files:
 z=json.loads(f.read_text());seen.add((z['world'],z['m']))
 z['quadrature_status']=f"requested fresh-source Gauss order{z['GL']}; inherited cache provenance in source_metadata; selected separate128→160 pilot; not an interval bound"
 z['precision_scope']='dps labels source assembly/output precision; original input cache provenance and eigensolver method remain separate; no interval eigenvalue bound'
 if 'effective_source_dps' not in z:
  orig=z['source_metadata']['origin'];d=orig.get('input_dps');h=re.findall(r'dps(\d+)',json.dumps(orig));d=d if isinstance(d,int) else min(map(int,h)) if h else z['dps'];z['effective_source_dps']=min(d,z['dps'])
 # Exact values, source hashes and measured timings are unchanged.
 tmp=f.with_suffix('.json.tmp');tmp.write_text(json.dumps(z,indent=2)+'\n');tmp.replace(f)
 methods[z['eigenvalue_method']]+=1
 rows.append(dict(world=z['world'],m=z['m'],file=f.name,sha256=hashlib.sha256(f.read_bytes()).hexdigest(),source_dps=z['dps'],effective_source_dps=z['effective_source_dps'],requested_GL=z['GL'],method=z['eigenvalue_method'],eigen_solver_bits=z.get('eigen_solver_bits'),float_matrix_difference_Frobenius=z['float_matrix_difference_Frobenius'],float_numeric_radius=z['float_numeric_radius'],matrix_source_kind=z['source_metadata']['origin']['kind']))
expected={(w,m) for w in ['zeta','plant'] for m in range(16,121)};assert seen==expected,(expected-seen,seen-expected)
assert all(r['float_matrix_difference_Frobenius']<r['float_numeric_radius'] for r in rows)
with (P/'RECEIPT_HASHES.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
# Source coefficients are computed once per process; ensure unchanged between batches.
cs={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in P.glob('*_coefficients_dps100.json')};assert len(set(cs.values()))==1
summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',complete=True,worlds=['zeta','plant'],m_range=[16,120],full_spectra=210,method_counts=dict(methods),all_float_source_comparison_guards_pass=True,max_float_difference_over_guard=max(r['float_matrix_difference_Frobenius']/r['float_numeric_radius'] for r in rows),all_coefficient_batches_identical=True,coefficient_file_sha256=cs,quadrature_validation_scope='m65:100dps128→160; no paired high-end source quadrature refinement was run',solver_validation_scope='approxACB400 vs independentMP references at m65,m120; no interval bounds',metadata_correction='genericGL128 wording corrected in priorityGL160 receipts; no numerical values changed',coverage_does_not_upgrade='E,delta,Schur/projectors remain their original separate precision')
(P/'COVERAGE.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
