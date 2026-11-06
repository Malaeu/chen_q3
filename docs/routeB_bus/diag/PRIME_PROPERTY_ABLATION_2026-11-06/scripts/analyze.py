# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "matplotlib"]
# ///
"""Render finite diagnostics and apply the immutable preregistered decisions."""
from pathlib import Path
import csv, json, math, re
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
COLORS = dict(S0='#111111', S1='#d55e00', S2='#009e73', S3='#cc79a7', S4='#0072b2', S5='#e69f00')

def read(path):
    with path.open() as f:
        rows = list(csv.DictReader(f))
    return {k: np.asarray([float(r[k]) for r in rows]) for k in rows[0]}

def slope(d, hi=1e7):
    m = (d['X'] >= 1e3*(1-1e-12)) & (d['X'] <= hi*(1+1e-12))
    return float(np.polyfit(np.log(d['X'][m]), np.log(d['W'][m]), 1)[0])

def main():
    grids = {p.stem: read(p) for p in sorted(ROOT.glob('S*.csv')) if re.fullmatch(r'S[05]|S[134]_seed[0-9]+|S2_y[0-9]+_seed[0-9]+',p.stem)}
    expected = 1+5+9+3+5+1
    assert len(grids) == expected, (len(grids), list(grids))
    summary = {}
    for name,d in grids.items():
        assert np.all(np.isfinite(d['W'])) and np.all(d['W']>=0)
        m=d['X']>=1e3*(1-1e-12)
        summary[name]=dict(X_max=float(d['X'][-1]),M_final=float(d['M'][-1]),W_final=float(d['W'][-1]),W_min=float(d['W'][m].min()),W_max=float(d['W'][m].max()),W_mean=float(d['W'][m].mean()),slope_common=slope(d),slope_full=slope(d,d['X'][-1]))
    quantiles={}
    for name in grids:
        d=read(ROOT/f'{name}_samples.csv');x=d.get('x',d.get('X'));r=d.get('ratio',d.get('M_over_sqrt_x'));r=r[(x>=1e3)&(x<=1e7)]
        quantiles[name]=dict(zip(['q01','q05','q25','q50','q75','q95','q99'],map(float,np.quantile(r,[.01,.05,.25,.5,.75,.95,.99]))))
    (ROOT/'QUANTILES_COMMON.json').write_text(json.dumps(quantiles,indent=2)+'\n')
    b=summary['S0']; s4=[v for k,v in summary.items() if k.startswith('S4')]; s1=[v for k,v in summary.items() if k.startswith('S1')]
    samples=read(ROOT/'S5_samples.csv'); sx=samples.get('x',samples.get('X')); ratio=samples.get('ratio',samples.get('M_over_sqrt_x'))
    mean=float(np.mean(ratio[(sx>=1e3)&(sx<=1e8)]))
    a5=max(((abs(v['slope_common']-b['slope_common']),k) for k,v in summary.items() if k!='S0'))
    decisions={
      'A1':dict(hit=b['W_min']>=.01 and b['W_max']<=1 and b['slope_full']<=0, **{k:b[k] for k in ['W_min','W_max','slope_full']}),
      'A2':dict(hit=all(v['W_max']<=1 for v in s4) and np.mean([v['W_mean'] for v in s4])<b['W_mean'],S4_mean=float(np.mean([v['W_mean'] for v in s4])),S0_mean=b['W_mean'],S4_max=max(v['W_max'] for v in s4)),
      'A3':dict(hit=all(v['W_max']<=1 for v in s1),S1_max=max(v['W_max'] for v in s1)),
      'A4':dict(hit=abs(mean-(-.6847652360899365))<=.15,mean=mean,target=-.6847652360899365),
      'A5':dict(hit=a5[0]>.1,max_slope_difference=a5[0],system=a5[1])}
    # Explicit Python bool conversion for JSON (numpy scalars otherwise leak).
    for d in decisions.values(): d['hit']=bool(d['hit']);d['verdict']='HIT' if d['hit'] else 'MISS'
    (ROOT/'ANALYSIS.json').write_text(json.dumps(dict(systems=summary,predictions=decisions),indent=2)+'\n')
    with (ROOT/'SYSTEM_SUMMARY.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=['system']+list(b));w.writeheader()
        for k,v in summary.items():w.writerow(dict(system=k,**v))
    fig,ax=plt.subplots(figsize=(12,7));seen=set()
    for name,d in grids.items():
        s=name[:2]; ax.plot(d['X'],d['W'],color=COLORS[s],lw=2.2 if s in ('S0','S5') else 1,alpha=1 if s in ('S0','S5') else .55,label=s if s not in seen else None);seen.add(s)
    ax.set(xscale='log',yscale='log',xlabel='X',ylabel='W(X)',title='Prime-property ablation: finite weak-Mertens functional')
    ax.legend(ncol=6);ax.grid(alpha=.2,which='both');fig.tight_layout();fig.savefig(ROOT/'W_ALL.png',dpi=170);fig.savefig(ROOT/'W_ALL.svg');plt.close(fig)
    fig,axes=plt.subplots(2,3,figsize=(13,7),sharex=True,sharey=True)
    # Identical comparison range; each seed gets equal weight via equal sample count.
    for s,ax in zip(COLORS,axes.flat):
        arrays=[]
        for name in grids:
            if not name.startswith(s):continue
            d=read(ROOT/f'{name}_samples.csv');x=d.get('x',d.get('X'));r=d.get('ratio',d.get('M_over_sqrt_x'));arrays.append(r[(x>=1e3)&(x<=1e7)])
        vals=np.concatenate(arrays);ax.hist(vals,bins=np.linspace(-5,5,101),weights=np.ones(len(vals))/len(vals)/.1,color=COLORS[s],alpha=.75)
        outside=int(np.count_nonzero((vals < -5)|(vals > 5)))
        ax.set_title(f'{s}: {len(arrays)} realization(s); outside ±5: {outside}')
        ax.set_xlabel('M(x) / sqrt(x)');ax.set_ylabel('density');ax.grid(alpha=.2)
    fig.suptitle('Log-uniform samples on common [1e3, 1e7]; seeds pooled equally')
    fig.tight_layout();fig.savefig(ROOT/'M_NORMALIZED_HISTOGRAMS.png',dpi=170);fig.savefig(ROOT/'M_NORMALIZED_HISTOGRAMS.svg');plt.close(fig)
    plant=read(ROOT/'S0_planted.csv')
    fig,ax=plt.subplots(figsize=(9,5))
    ax.loglog(grids['S0']['X'],grids['S0']['W'],label='S0',color=COLORS['S0'])
    ax.loglog(plant['X'],plant['W'],label='S0 + planted off-line exponent 0.8',color='#b2182b')
    ax.axvspan(1e5,1e7,color='grey',alpha=.1,label='J4 regression window')
    ax.set(xlabel='X',ylabel='W(X)',title='Planted control: sensitivity to super-square-root growth')
    ax.legend();ax.grid(alpha=.2);fig.tight_layout();fig.savefig(ROOT/'PLANTED_CONTROL.png',dpi=170);plt.close(fig)
    fig,axes=plt.subplots(1,2,figsize=(12,5))
    seen=set()
    for name,d in grids.items():
        s=name[:2]
        if s not in ('S1','S2','S3'):continue
        label=s if s not in seen else None;seen.add(s)
        axes[0].semilogx(d['X'],d['N_over_x'],color=COLORS[s],alpha=.5,label=label)
        axes[1].semilogx(d['X'],d['count_error']/np.sqrt(d['X']),color=COLORS[s],alpha=.5)
    axes[0].set(xlabel='x',ylabel='N(x) / x');axes[0].legend()
    axes[1].set(xlabel='x',ylabel='(N(x) - rho_hat*x) / sqrt(x)')
    fig.suptitle('Counting diagnostics; rho_hat fitted at 1e7, right-end error forced to zero')
    for ax in axes:ax.grid(alpha=.2)
    fig.tight_layout();fig.savefig(ROOT/'COUNTING_DIAGNOSTICS.png',dpi=170);plt.close(fig)
    print(json.dumps(decisions,indent=2))

if __name__=='__main__':main()
