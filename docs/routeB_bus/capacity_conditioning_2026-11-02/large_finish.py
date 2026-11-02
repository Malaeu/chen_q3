"""Complete continuous-cutoff holes using cached GL160 matrices and add row diagnostics."""
from pathlib import Path
import sys,json,csv
import mpmath as mp
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P.parent/'capacity_matrix_2026-11-02'));from capacity import Erow
from scan import serial
import importlib.util
spec=importlib.util.spec_from_file_location("poly_validation",P.parent/"quiet_space_kappa_2026-11-02/validation.py");poly=importlib.util.module_from_spec(spec);spec.loader.exec_module(poly)
m,cacheq=map(int,sys.argv[1:]);mp.mp.dps=160
path=P/f'cell_m{m}_dps120_gl128.json';d=json.loads(path.read_text());v=json.loads((P/f'large_validation_m{m}_q{cacheq}.json').read_text());A=mp.matrix(v['matrix_A']);ae=mp.eigsy(A,eigvals_only=True)
z=[mp.mpf(r['gamma']) for r in csv.DictReader((P.parent/'capacity_matrix_2026-11-02/zeros.csv').open())];L=mp.log(m);Omega=2*mp.pi*m/L
qlo=sum(g<Omega for g in z);qhi=sum(g<mp.mpf('1.4')*Omega for g in z);existing={r['q'] for r in d['all_sectors']};holes=sorted(set(range(qlo,qhi+1))-existing)
for q in holes:
 Q=poly.poly_kernel(m,q,z);r=m+1-q;X=A*Q;val=mp.eigsy(X.T*X,eigvals_only=True);delta=mp.sqrt(val[val.rows-1]);mu=delta*mp.mpf('1.000001');count=sum(x<mu for x in ae)
 row=dict(m=m,q=q,r=r,kappas=[],delta=delta,adaptive_mu=mu,signed_count=count,count_minus_r=count-r,saturates=count==r,lambda_r=ae[r],lambda_r_over_delta=ae[r]/delta,lambda_r_minus_delta=ae[r]-delta,lambda_r_minus_mu=ae[r]-mu,minimum_raw_singular_value=None,raw_condition=None,supplement_kernel_method='independent polynomial divisibility; raw conditioning omitted for nonpassing state',supplement_working_dps=160,supplement_matrix_entry_digits=150,supplement_order=160)
 if count==r:raise RuntimeError(('new passing hole needs full detail',m,q))
 d['all_sectors'].append(serial(row,150));print('filled',m,q,count-r,flush=True)
for r in d['passing_sectors']:
 q=r['q'];E=mp.matrix([Erow(t,m) for t in z[:q]]);norms=[mp.norm(E[j,:]) for j in range(q)];a,b=[i-1 for i in r['top_adjacent_pair_indices']];weak=list(map(mp.mpf,r['weak_left_vector']));order=sorted(range(q),key=lambda i:abs(weak[i])**2,reverse=True)
 r['row_norms']=[mp.nstr(x,120) for x in norms];r['adjacent_pair_row_normalized_correlation']=mp.nstr(abs(mp.fdot(E[a,:],E[b,:]))/(norms[a]*norms[b]),120);r['top_two_mass_indices']=[order[0]+1,order[1]+1];r['top_two_mass']=mp.nstr(abs(weak[order[0]])**2+abs(weak[order[1]])**2,120);r['top_adjacent_pair_signed_component_product']=mp.nstr(weak[a]*weak[b],120)
for group in ['all_sectors','passing_sectors']:
 for r in d[group]:
  q=r['q'];r['continuous_kappa_lower']=mp.nstr(max(mp.mpf(1),z[q-1]/Omega),120);r['continuous_kappa_upper']=mp.nstr(min(mp.mpf('1.4'),z[q]/Omega),120)
 d[group].sort(key=lambda r:r['q'])
d['continuous_q_coverage']=list(range(qlo,qhi+1));d['supplemented_grid_holes']=holes;d['continuous_q_coverage_complete']=True
path.write_text(json.dumps(d,indent=2)+'\n')
