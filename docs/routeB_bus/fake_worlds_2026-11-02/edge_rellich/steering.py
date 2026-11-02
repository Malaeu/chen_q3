"""Owner follow-up: K1, four weak pieces, fixed-subset tests, prolate.
No eigensolver, fitted coefficients, or new directions.
"""
from pathlib import Path
import json,csv,itertools,sys
import mpmath as mp
import rellich as r
P=Path(__file__).resolve().parent;r.IN=Path(sys.argv[1]);mp.mp.dps=110
cells=[json.loads(p.read_text()) for p in sorted((P/'cells').glob('*_o192.json'))]
assert len(cells)==21
cells.sort(key=lambda d:(d['world']!='zeta',d['m'],d['q']))
rows=[];details=[]
for d in cells:
    world,m=d['world'],d['m'];L=mp.log(m);b=L/2;fb=mp.mpf(d['f_b']);lam=mp.mpf(d['lambda']);T=mp.mpf(d['T']);edge=fb**2*mp.log(T)/(mp.pi*T)
    _,_,_,_,f,_,_=r.load_case(r.IN/d['input']);f/=mp.norm(f);ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
    sc=[mp.mpf(0)]*(m+1)
    for i in range(1,m+1):sc[i]-=f[i]**2/(mp.pi*i)
    for i in range(m+1):
        for j in range(i+1,m+1):
            v=2*f[i]*f[j]*ds[i]*ds[j]/(mp.pi*(i*i-j*j));sc[j]+=v*j;sc[i]-=v*i
    probe=mp.mpf(0);preg=mp.mpf(0);bc=r.coeffs(m,world)
    for n in range(2,m+1):
        if not bc[n]:continue
        s=mp.log(n);co=mp.cos(2*mp.pi*s/L);si=mp.sin(2*mp.pi*s/L);cn=mp.mpf(1);sn=mp.mpf(0);Q=mp.mpf(0);fpa=mp.mpf(0)
        for k in range(m+1):
            omega=2*mp.pi*k/L
            Q+=2*f[k]**2*(1-s/L)*cn+sc[k]*sn
            fpa+=ds[k]*f[k]*omega*sn/mp.sqrt(L)
            cn,sn=cn*co-sn*si,sn*co+cn*si
        if n==m:Q=mp.mpf(0);fpa=mp.mpf(0)
        weight=bc[n]/mp.sqrt(n);probe+=weight*s*Q
        a=b-s;preg+=2*weight*fb*(b*b-a*a)*fpa
    own=lam*L*fb**2;finite=d['finite'];weak=d['physical_weak']
    k1={'residual_norm':finite['residual_norm'],
        'twice_r_Xf':mp.mpf(finite['volume'])-own,
        'defect_matrix_rank':1,'defect_matrix_operator_norm':2*m+1,
        'defect_f_contraction':L*fb**2,
        'defect_r_f_contraction':mp.mpf(finite['boundary_subtracted'])-own,
        'commutator':finite['commutator']}
    pieces={'arch':mp.mpf(weak['volume_arch']),
            'prime':mp.mpf(weak['volume_arithmetic']),
            'pole':mp.mpf(weak['volume_pole']),
            'jump_defect':mp.mpf(weak['boundary'])}
    assert abs(sum(pieces.values())-mp.mpf(weak['total']))<mp.mpf('1e-85')
    prolate={'finite_commutator_exact':0,'symmetric_form_commutator_exact':0,
             'arch_interior_maximal_anomaly':L*fb**2,
             'prime_regular_volume':preg,'prime_shifted_jump':-preg,
             'pole_commutator_exact':0,'scalar_commutator_exact':0,
             'arch_outer_distribution_defect':-L*fb**2,
             'combined_form_bookkeeping_total_exact':0,
             'finite_zero_head_form_commutator_exact':0,
             'finite_zero_prefix_form_commutator_exact':0,
             'form_source_balance_above_T_exact':0,
             'form_source_balance_beyond_census_exact':0,
             'interior_arch_anomaly_zero_tail_scope':'NOT_OBTAINED_BY_TERMWISE_FINITE_ZERO_COMMUTATORS; NONUNIFORM_ENDPOINT_LIMIT_REQUIRES_REGULARIZATION',
             'interior_anomaly_over_lambda':L*fb**2/lam,
             'R_after_imposed_edge_rescaling':lam/edge,
             'scope':'EXACT_GREEN_AND_DISTRIBUTION_IDENTITIES_WITH_NUMERICAL_TRACE_EVALUATION; NOT_AN_INDEPENDENT_LAMBDA_LAW'}
    row={'world':world,'m':m,'q':d['q'],'mode':d['mode'],'lambda':lam,'edge_scale':edge,'R_original':lam/edge,
         **{k+'_piece':v for k,v in pieces.items()},'weak_total':weak['total'],
         'prime_log_weighted_Q_probe_NOT_commutator':probe,
         'K1_residual_norm':k1['residual_norm'],'K1_twice_r_Xf':k1['twice_r_Xf'],
         'K1_defect_r_f':k1['defect_r_f_contraction'],
         'prolate_arch_anomaly':prolate['arch_interior_maximal_anomaly'],
         'prolate_prime_regular_volume':preg,'prolate_prime_shifted_jump':-preg,
         'prolate_total_form_commutator_exact':0}
    rows.append(row);details.append({'input':d['input'],'K1':k1,'four_weak_pieces':pieces,'prime_log_weighted_Q_probe_NOT_commutator':probe,'prolate':prolate})
keys=['arch','prime','pole','jump_defect'];combos=[]
for count in range(1,5):
    for subset in itertools.combinations(keys,count):
        tests=[]
        for row in rows:
            if row['world']!='zeta':continue
            value=sum(mp.mpf(row[k+'_piece']) for k in subset);la=mp.mpf(row['lambda']);target=4*row['edge_scale']
            tests.append({'m':row['m'],'q':row['q'],'value':value,
                          'relative_error_to_lambda':abs(value-la)/abs(la),
                          'relative_error_to_4edge':abs(value-target)/abs(target)})
        combos.append({'subset':list(subset),'passes_all_8_lambda_10pct':all(t['relative_error_to_lambda']<=mp.mpf('.1') for t in tests),
                       'passes_all_8_4edge_10pct':all(t['relative_error_to_4edge']<=mp.mpf('.1') for t in tests),
                       'max_relative_error_to_lambda':max(t['relative_error_to_lambda'] for t in tests),'cells':tests})
assert all(r.coeffs(d['m'],d['world'])[d['m']]==0 for d in cells)
with (P/'weak_four_pieces.csv').open('w',newline='') as f:
    wr=csv.DictWriter(f,fieldnames=rows[0]);wr.writeheader();wr.writerows({k:r.serial(v) for k,v in row.items()} for row in rows)
result={'status':'DIAGNOSTIC_NEVER_A_PROOF','owner_steering_after_initial_run':True,'cells':details,'fixed_subsets_tested':15,
        'lambda_10pct_successful_subsets':[c['subset'] for c in combos if c['passes_all_8_lambda_10pct']],
        '4edge_10pct_successful_subsets':[c['subset'] for c in combos if c['passes_all_8_4edge_10pct']],
        'subset_tests':combos,'birth_coefficient_zero_on_all_requested_cells':True,'new_eigenproblems':0}
(P/'STEERING.json').write_text(json.dumps(r.serial(result),indent=2)+'\n')
print(json.dumps({'successful_lambda_subsets':result['lambda_10pct_successful_subsets'],'successful_4edge_subsets':result['4edge_10pct_successful_subsets'],
                  'best_max_relative_error_lambda':r.serial(min(c['max_relative_error_to_lambda'] for c in combos))}))
