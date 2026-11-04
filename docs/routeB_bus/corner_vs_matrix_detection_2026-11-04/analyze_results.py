#!/usr/bin/env python3
"""Aggregate SAVED diagnostics; no matrix builds or eigenproblems."""
import csv, hashlib, json, math
from fractions import Fraction
from pathlib import Path
import numpy as np
P=Path(__file__).resolve().parent

def read(n): return json.loads((P/n).read_text())
def write(n,x): (P/n).write_text(json.dumps(x,indent=2)+'\n')
def csvout(n,rows):
    with (P/n).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader();w.writerows(rows)

def main():
    assert read('gate/gate.json')['pass']
    assert read('predecessor_recheck.json')['status']=='ALL_9_LATER_THRESHOLDS_PREDECESSORS_RECHECKED'
    prefix=read('prefix_summary.json'); assert prefix['status']=='COMPLETE_INTEGER_FIRST_DETECTIONS'
    corner={(r['a'],r['gamma']):r for r in read('corner_summary.json')['cases']}
    cells={int(p.stem[1:]):json.loads(p.read_text()) for p in (P/'matrix_cells').glob('m*.json')}
    rows=[]
    for g in prefix['groups']:
        for a,m in g['first'].items():
            # Every eligible predecessor was actually calculated for this case.
            for mm in range(g['m_admit'],m+1):
                case=next(r for r in cells[mm]['cases'] if r['a']==a and r['gamma']==g['gamma'])
                assert case['detected']==(mm==m)
            c=corner[a,g['gamma']]; d=next(r for r in cells[m]['cases'] if r['a']==a and r['gamma']==g['gamma'])
            mp=read(f"confirmation/g{g['gamma']}_a{a.replace('/','_')}_m{m}.json")
            assert float(mp['total_rayleigh']) < -1e-6
            rows.append(dict(a=a,gamma=g['gamma'],m_admit=g['m_admit'],m_matrix=m,
                m_corner=c['m_corner'] if c['m_corner'] is not None else '>3000',
                matrix_lambda_float=d['lambda_min'],MP_rayleigh=mp['total_rayleigh'],
                peak_mode=d['peak_mode'],peak_frequency=d['peak_frequency'],frequency_bin=d['frequency_bin'],
                gamma_above_Omega=d['gamma_above_Omega'],delay=m-g['m_admit'],
                D1_supported=m<(c['m_corner'] or 3001),
                D2_delay_pass=m-g['m_admit']<=max(2,.05*g['m_admit']),D3_pass=d['peak_within_one_bin']))
    rows.sort(key=lambda r:(float(Fraction(r['a'])),r['gamma']))
    csvout('thresholds.csv',rows)
    controls=[]
    for m,c in sorted(cells.items()):
        baseline=c['unplanted_lambda_min']; assert baseline>=-1e-12
        a0=[r for r in c['cases'] if r['a']=='0'];assert all(not r['detected'] and r['corner_float']>=0 for r in a0)
        # All admitted a=0 controls remain present even when resolved positive cases are skipped.
        admitted=[g for g in (14,50,200,800) if c['T']>g]; assert sorted(r['gamma'] for r in a0)==admitted
        controls.append(dict(m=m,baseline_lambda=baseline,a0_count=len(a0),
                             a0_min_lambda=min(r['lambda_min'] for r in a0),
                             a0_detections=0,case_count=len(c['cases'])))
    csvout('controls.csv',controls)
    core=read('core/core_results.json'); cr=core['rows']
    def series(world,kind,a='0',gamma='',convention=None):
        return sorted([r for r in cr if r['world']==world and r['kind']==kind and str(r['a'])==a and str(r['gamma'])==str(gamma) and (convention is None or r['convention']==convention)],key=lambda r:r['m'])
    def fit(rs):
        tail=[r for r in rs if r['m']>=512]; assert len(tail)>=3 and all(r['value']>0 for r in tail)
        slope,intercept=np.polyfit(np.log([r['m'] for r in tail]),np.log([r['value'] for r in tail]),1)
        return dict(m=[r['m'] for r in tail],slope=float(slope),ratio_3000_to_512=next(r['value'] for r in tail if r['m']==3000)/next(r['value'] for r in tail if r['m']==512))
    z=series('zeta','Cstar_original_B');dh=series('dh','Cstar_original_B')
    k2={}
    for gamma in (14,50):
        f=fit(series('zeta','Cstar_effective_B_minus_Q','1/3',gamma));f['pass']=.2<=f['slope']<=.47 and f['ratio_3000_to_512']>1;k2[str(gamma)]=f
    k4=fit(dh); k4['pass']=k4['ratio_3000_to_512']>=2 and k4['slope']>=.1;k4['any_C_above_16']=any(r['value']>16 for r in dh)
    csvout('CSTAR_SUMMARY.csv',[{k:r.get(k,'') for k in ['m','world','kind','a','gamma','convention','value','eigenpair_residual','normalized_constraint_residual']} for r in cr if r['kind'].startswith('Cstar')])
    weak=read('weak_confirmation_summary.json'); assert len(weak['rows'])==14
    weak_rows=[]
    for r in weak['rows']:
        assert float(r['rayleigh']) < -1e-6
        f=core['first_weak_detections'][r['key']]; assert f['is_first_admitted'] and r['m']==f['first_m']
        weak_rows.append(dict(a=r['a'],gamma=r['gamma'],convention=r['convention'],m_core=r['m'],m_corner='>3000',float_value=f['value'],MP_rayleigh=r['rayleigh'],MP_constraint_residual=r['constraint_residual']))
    csvout('weak_thresholds.csv',weak_rows)
    scalar=read('core/scalar_summary.json');assert all(r['first_negative_m'] is None for r in scalar['cases'])
    dhd=read('dh_detection.json'); assert dhd['first_m']==55 and float(dhd['high_precision_rayleigh'])<-1e-6
    scores=dict(honesty='DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER / NOT_RH; D0 unchanged',
        D1=dict(supported=sum(r['D1_supported'] for r in rows),total=12,censored_corners=11),
        D2=dict(conditional_flatness_pass=sum(r['D2_delay_pass'] for r in rows),total=12,verdict='UNIVERSAL_PREDICTION_FAILS',corner_growth='Only gamma14,a1/3 crosses; remaining corners censored, full ordering not established'),
        D3=dict(pass_count=sum(r['D3_pass'] for r in rows),total=12,verdict='UNIVERSAL_PREDICTION_FAILS'),
        K1=dict(max_C=max(r['value'] for r in z),tested_m=[r['m'] for r in z],pass_on_tested_grid=all(r['value']<=16 for r in z)),
        K2=k2,K3=dict(finite_conjunction_supported=True,all_14_MP_witnesses_negative=True,unplanted_already_fires=True,not_offline_specific=True),K4=k4,
        DH=dict(first_matrix=55,corner='>3000',MP_rayleigh=dhd['high_precision_rayleigh']),
        controls=dict(matrix_m_count=len(controls),actual_m=[r['m'] for r in controls],baseline_min=min(r['baseline_lambda'] for r in controls),a0_count=sum(r['a0_count'] for r in controls),a0_min=min(r['a0_min_lambda'] for r in controls),all_pass=True),
        scope='Corners exhaustive eligible integers16..3000; matrix consecutive prefixes to detections plus checkpoints; C* only declared25-point grid; point arithmetic, not interval certificate')
    write('SCORES.json',scores)
    try:
        import matplotlib; matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        fig,ax=plt.subplots(1,2,figsize=(11,4))
        for a in ('1/20','1/10','1/3'):
            rr=[r for r in rows if r['a']==a]; ax[0].plot([r['gamma'] for r in rr],[r['m_matrix'] for r in rr],'o-',label=a)
        ax[0].set(xlabel='quartet height gamma',ylabel='first matrix detection m');ax[0].legend(title='a');ax[0].set_xscale('log');ax[0].set_yscale('log')
        for label,rr in [('zeta',z),('DH',dh)]+[(f'plant a=1/3 gamma={g}',series('zeta','Cstar_effective_B_minus_Q','1/3',g)) for g in (14,50)]:
            ax[1].loglog([r['m'] for r in rr],[r['value'] for r in rr],'.-',label=label)
        ax[1].set(xlabel='m',ylabel='C* (raw quotient)');ax[1].legend(fontsize=8)
        fig.suptitle('DIAGNOSTIC_NEVER_A_PROOF');fig.tight_layout();fig.savefig(P/'detectors_and_cores.png',dpi=150);plt.close(fig)
    except ImportError: pass
    print(json.dumps(scores,indent=2))
if __name__=='__main__': main()
