"""Scalar integration and preregistered finite scaling comparison; no eigensolve."""
from pathlib import Path
from collections import Counter
import csv,json,hashlib,argparse,math
import numpy as np
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=100
def yes(v):return str(v).lower()=='true'
def val(v,n=12):return mp.nstr(mp.mpf(v),n) if v not in ('',None) else ''
def logabs(v):return float(mp.log10(abs(mp.mpf(v))))
def read(path):return list(csv.DictReader(path.open()))
def write(name,rows):
    with (P/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(dict.fromkeys(k for r in rows for k in r)));w.writeheader();w.writerows(rows)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--complete',action='store_true');a=ap.parse_args()
    s=read(P/'spectra/spectra.csv');raw=read(P/'roots/summary.csv');root=[r for r in raw if r['cutoff']=='fixed_c1_4'];lookup={(r['world'],int(r['m'])):r for r in s}
    expected={(w,m) for w in ['zeta','dh','plant'] for m in range(16,301)}
    even={(r['world'],int(r['m'])):r for r in root if r['parity']=='even'}
    full={(r['world'],int(r['m'])):r for r in root if (r['world'],int(r['m'])) in lookup and r['parity']==lookup[r['world'],int(r['m'])]['global_ground_parity']}
    replay_ok={'PHYSICAL_STRIP_NEWTON_LOW_HIGH_REPLAY','ALL_ROOT_NEWTON_LOW_HIGH_REPLAY','COMPLETE_LOW_HIGH_POLYNOMIAL_ROOT_REPLAY'}
    def valid_replay(r):
        value=r.get('observed_low_high_max_root_shift')
        if value in (None,'') or r.get('replay_status') not in replay_ok:return False
        try:
            x=mp.mpf(value)
            return bool(mp.isfinite(x) and x>=0 and int(r['replay_missing_strip_root_count'])==0)
        except (ValueError,TypeError,KeyError):return False
    if a.complete:
        assert len(raw)==len({(r['world'],int(r['m']),r['parity'],r['cutoff']) for r in raw}), 'Duplicate root/cutoff rows'
        assert len(s)==855 and set(lookup)==expected and set(even)==expected and set(full)==expected
        assert all(yes(r['ground_resolved']) for r in s)
        assert all(yes(r['ground_resolved']) and valid_replay(r) for r in raw), 'Incomplete or unavailable actual LOW/HIGH replay'
    gaps=[]
    for r in sorted(s,key=lambda x:(x['world'],int(x['m']))):
        d={k:r[k] for k in ['world','m','global_ground_parity','ground_resolved']}
        for k in ['lambda_even0','lambda_even1','lambda_odd0','lambda_odd1','even_gap','odd_gap','parity_gap','global_gap']:d[k]=val(r[k])
        lo=mp.mpf(r['lambda_'+r['global_ground_parity']+'0']);d['global_gap_over_abs_ground']=val(mp.mpf(r['global_gap'])/abs(lo)) if lo else ''
        d['lambda_even1_sign_resolved']=r.get('lambda_even1_sign_resolved');d['lambda_odd1_sign_resolved']=r.get('lambda_odd1_sign_resolved');gaps.append(d)
    write('GAPS.csv',gaps)
    dig=[]
    for r in sorted(root,key=lambda x:(x['world'],int(x['m']),x['parity'])):
        key=r['world'],int(r['m'])
        if r['parity']!='even' and full.get(key)!=r:continue
        d={k:r.get(k) for k in ['world','m','parity','global_parity','is_full_ground','source_count','source_nonreal_count','source_nonreal_missing_at_1e_6','polynomial_strip_count','forced_external_count','fourier_strip_count','fourier_nonreal_count','polynomial_pure_imaginary_count','polynomial_nonreal_all_count','polynomial_nonreal_outside_strip_below_T','matched_under_1e_6','source_unrecovered_at_1e_6']}
        for k in ['T','polynomial_only_max_abs_deviation','observed_low_high_max_root_shift']:d[k]=val(r.get(k))
        dig.append(d)
    write('ZERO_SUMMARY.csv',dig)
    control_scaling=[]
    for (world,m),r in sorted(full.items()):
        if world=='zeta':continue
        deviation=mp.mpf(r['polynomial_only_max_abs_deviation']);height=mp.mpf(r['T'])
        control_scaling.append(dict(world=world,m=m,parity=r['parity'],max_numerator_source_deviation=val(deviation),T=val(height),deviation_over_T=val(deviation/height),source_count=r['source_count'],matches_1e_6=r['matched_under_1e_6'],close_fraction=val(mp.mpf(r['matched_under_1e_6'])/int(r['source_count']))))
    write('CONTROL_SCALING.csv',control_scaling)
    models={'m_over_log_m_squared':lambda x:x/np.log(x)**2,'m_over_log_m':lambda x:x/np.log(x),'sqrt_m':np.sqrt,'log_m_squared':lambda x:np.log(x)**2,'m':lambda x:x}
    zrows=[r for r in even.values() if r['world']=='zeta'];zrows.sort(key=lambda r:int(r['m']));fit=[]
    usable=[r for r in zrows if valid_replay(r) and mp.mpf(r['polynomial_only_max_abs_deviation'])>100*max(mp.mpf(r['observed_low_high_max_root_shift']),mp.mpf('1e-150'))]
    ms=np.array([int(r['m']) for r in usable],float);ys=np.array([-logabs(r['polynomial_only_max_abs_deviation']) for r in usable]);train=(ms>=40)&(ms<=160);test=(ms>=161)&(ms<=300)
    if np.sum(train)>=3 and np.sum(test)>=1:
        for name,f in models.items():
            x=f(ms);X=np.column_stack([x,np.ones(len(x))]);coef=np.linalg.lstsq(X[train],ys[train],rcond=None)[0];err=X@coef-ys
            fit.append(dict(model=name,training='40..160',held_out='161..300',training_cells=int(np.sum(train)),held_out_cells=int(np.sum(test)),slope=coef[0],intercept=coef[1],training_RMSE_decades=float(np.sqrt(np.mean(err[train]**2))),held_out_RMSE_decades=float(np.sqrt(np.mean(err[test]**2))),held_out_MAE_decades=float(np.mean(abs(err[test]))),held_out_max_abs_error_decades=float(max(abs(err[test]))),predicted_log10_deviation_m300=float(-np.dot([f(np.array([300.]))[0],1],coef))))
        fit.sort(key=lambda r:r['held_out_RMSE_decades']);write('SCALING.csv',fit)
    edge_fit=[]
    if len(ms):
        reference=[mp.mpf(r['gamma']) for r in read(P/'inputs/zeta_zeros.csv')]
        phase=[]
        for r in usable:
            m=int(r['m']);T=mp.mpf(r['T']);last=max(g for g in reference if g<T)
            phase.append(float((T-last)*mp.log(m)/(2*mp.pi)))
        phase=np.array(phase);tail=(ms>=261)&(ms<=299)
        if np.sum(train)>=3 and np.sum(tail):
            for name in ['m_over_log_m_squared','sqrt_m']:
                x=models[name](ms);X=np.column_stack([x,phase,np.ones(len(x))]);coef=np.linalg.lstsq(X[train],ys[train],rcond=None)[0];err=X@coef-ys
                base=np.column_stack([x,np.ones(len(x))]);cb=np.linalg.lstsq(base[train],ys[train],rcond=None)[0];eb=base@cb-ys
                edge_fit.append(dict(model=name+' plus edge_phase',scope='Exploratory after early held-out peek; new untouched tail261..299 excludes pilot300',training='40..160',new_tail='261..299',tail_cells=int(np.sum(tail)),slope=coef[0],edge_phase_coefficient=coef[1],intercept=coef[2],baseline_tail_RMSE_decades=float(np.sqrt(np.mean(eb[tail]**2))),edge_tail_RMSE_decades=float(np.sqrt(np.mean(err[tail]**2)))))
            write('SCALING_EDGE.csv',edge_fit)
    stats={};odd_ranges=[]
    for world in ['zeta','dh','plant']:
        ss=sorted([r for r in s if r['world']==world],key=lambda r:int(r['m']));rr=[r for r in full.values() if r['world']==world];ee=[r for r in even.values() if r['world']==world]
        def first(pred,rows=ss):return next((int(r['m']) for r in rows if pred(r)),None)
        odd=[int(r['m']) for r in ss if r['global_ground_parity']=='odd'];runs=[]
        for m in odd:
            if not runs or m!=runs[-1][-1]+1:runs.append([m,m])
            else:runs[-1][-1]=m
        odd_ranges.append(dict(world=world,odd_global_m_count=len(odd),odd_global_m_ranges=', '.join(str(x) if x==y else f'{x}-{y}' for x,y in runs)))
        stats[world]=dict(spectral_cells=len(ss),global_parities=dict(Counter(r['global_ground_parity'] for r in ss)),first_global_odd=first(lambda r:r['global_ground_parity']=='odd'),first_negative_even=first(lambda r:mp.mpf(r['lambda_even0'])<0),first_negative_odd=first(lambda r:mp.mpf(r['lambda_odd0'])<0),full_root_cells=len(rr),even_root_cells=len(ee),even_source_numerator_count_mismatches=[int(r['m']) for r in ee if int(r['source_count'])!=int(r['polynomial_strip_count'])],even_full_count_minus_source_minus_forced=[int(r['m']) for r in ee if int(r['fourier_strip_count'])-int(r['source_count'])-int(r['forced_external_count'])],first_source_nonreal_below_T=first(lambda r:int(r['source_nonreal_count'])>0,sorted(rr,key=lambda r:int(r['m']))),first_global_missing_source_at_1e_6=first(lambda r:int(r['source_unrecovered_at_1e_6'])>0,sorted(rr,key=lambda r:int(r['m']))),first_even_pure_imaginary=first(lambda r:int(r['polynomial_pure_imaginary_count'])>0,sorted(ee,key=lambda r:int(r['m']))),first_global_pure_imaginary=first(lambda r:int(r['polynomial_pure_imaginary_count'])>0,sorted(rr,key=lambda r:int(r['m']))),axis_parity_mismatch_cells=[int(r['m']) for r in ee if (int(r['polynomial_pure_imaginary_count'])>0)!=(r['global_parity']=='odd')],global_off_real_strip_cells=[int(r['m']) for r in rr if int(r['fourier_nonreal_count'])>0],global_off_axis_anywhere_cells=[int(r['m']) for r in rr if int(r['polynomial_nonreal_all_count'])>0],global_off_axis_outside_strip_below_T_cells=[int(r['m']) for r in rr if int(r['polynomial_nonreal_outside_strip_below_T'])>0],even_off_axis_anywhere_cells=[int(r['m']) for r in ee if int(r['polynomial_nonreal_all_count'])>0],global_nonreal_source_points_unrecovered=sum(int(r.get('source_nonreal_missing_at_1e_6') or 0) for r in rr))
    write('ODD_RANGES.csv',odd_ranges)
    summary=dict(status='COMPLETE_FINITE_DIAGNOSTIC' if a.complete else 'SNAPSHOT_NOT_COMPLETE',spectral_cells=len(s),expected_spectral_cells=855,even_root_cells=len(even),global_root_cells=len(full),worlds=stats,scaling=fit,exploratory_edge_scaling=edge_fit,scaling_candidate_preregistered='m_over_log_m_squared',scaling_scope='Finite held-out empirical comparison, not an asymptotic bound; error floors excluded.',source_CSV_sha256=hashlib.sha256((P/'spectra/spectra.csv').read_bytes()).hexdigest(),root_CSV_sha256=hashlib.sha256((P/'roots/summary.csv').read_bytes()).hexdigest(),route_state_changed=False)
    (P/'OVERVIEW.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k not in ['worlds','scaling']},indent=2))
    import matplotlib;matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig,ax=plt.subplots(1,2,figsize=(12,4.5));zz=sorted([r for r in s if r['world']=='zeta'],key=lambda r:int(r['m']))
    for field,label in [('lambda_even0','even ground'),('even_gap','even gap'),('global_gap','global gap')]:ax[0].plot([int(r['m']) for r in zz],[logabs(r[field]) for r in zz],label=label)
    ax[0].set(xlabel='literal m',ylabel='log10 absolute value',title='Zeta: absolute ground and gaps');ax[0].legend();ax[0].grid(alpha=.2)
    for i,w in enumerate(['zeta','dh','plant']):
        rr=sorted([r for r in s if r['world']==w],key=lambda r:int(r['m']));xx=[int(r['m']) for r in rr];yy=[i+.16*(1 if r['global_ground_parity']=='odd' else -1) for r in rr];cc=['#ce624e' if r['global_ground_parity']=='odd' else '#238a91' for r in rr];ax[1].scatter(xx,yy,c=cc,s=9)
    ax[1].set(xlabel='literal m',yticks=[0,1,2],yticklabels=['zeta','DH','plant'],title='Global ground parity: teal even, coral odd');fig.tight_layout();fig.savefig(P/'SPECTRAL_GAPS.png',dpi=180);fig.savefig(P/'SPECTRAL_GAPS.svg');plt.close(fig)
    fig,ax=plt.subplots(1,2,figsize=(12,4.5))
    for w,color in [('zeta','#238a91'),('dh','#ce624e'),('plant','#725a9c')]:
        rr=sorted([r for r in full.values() if r['world']==w],key=lambda r:int(r['m']));ax[0].plot([int(r['m']) for r in rr],[logabs(r['polynomial_only_max_abs_deviation']) for r in rr],label=w,color=color,lw=1)
    ax[0].set(xlabel='literal m',ylabel='log10 max displacement in min-sum pairing',title='Chosen min-sum pairing, fixed c=1/4');ax[0].legend();ax[0].grid(alpha=.2)
    if len(ms):ax[1].plot(ms,ys,'.',ms=2,label='zeta even: -log10 error')
    if fit:
        best=fit[0];pred=best['slope']*models[best['model']](ms)+best['intercept'];ax[1].plot(ms,pred,label=best['model']);ax[1].axvline(160,color='gray',ls='--',lw=1)
    ax[1].set(xlabel='literal m',ylabel='-log10 primary deviation',title='Fixed training boundary m=160');ax[1].legend();ax[1].grid(alpha=.2);fig.tight_layout();fig.savefig(P/'ZERO_FIDELITY.png',dpi=180);fig.savefig(P/'ZERO_FIDELITY.svg');plt.close(fig)
if __name__=='__main__':main()
