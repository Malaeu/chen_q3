"""Saved one-endpoint profiles, with primary-cutoff model limits labelled."""
from pathlib import Path
from collections import defaultdict
import os,csv
os.environ.setdefault('MPLCONFIGDIR','/tmp/ladder-matplotlib')
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
groups=defaultdict(list)
with (P/'spectra'/'scalar_profiles.csv').open() as f:
    for r in csv.DictReader(f):
        if int(r['cut'])==400 and int(r['mesh']) in [64,256]:groups[r['world'],int(r['mesh']),float(r['a'])].append(float(r['mu_endpoint']))
fig,axs=plt.subplots(1,2,figsize=(12,4.7),layout='constrained')
for ax,mesh in zip(axs,[64,256]):
    for world,label,color in [('poisson','Poisson','#d56e51'),('gue_bulk','GUE bulk','#655eaf'),('picket','Picket','#95751d'),('zeta_surrogate','Zeta <=400 + model tail','#087c83')]:
        cells=sorted((a,v) for (w,m,a),v in groups.items() if w==world and m==mesh)
        x=np.array([a for a,v in cells]);y=np.array([np.median(v) for a,v in cells])
        ax.plot(x,y,label=label,color=color)
        if len(cells[0][1])>1:ax.fill_between(x,[np.quantile(v,.25) for a,v in cells],[np.quantile(v,.75) for a,v in cells],alpha=.12,color=color)
    refs=[]
    with (P.parent/'extension_margin'/'uniform'/'single_endpoint.csv').open() as f:
        refs=[r for r in csv.DictReader(f) if r['world']=='zeta' and int(r['mesh'])==mesh and r['mu']]
    ax.plot([float(r['a']) for r in refs],[float(r['mu']) for r in refs],color='black',lw=1.5,label='Arithmetic zeta')
    ax.set(title=f'Delta=1/{mesh}',xlabel='old history length a',ylabel='one-endpoint margin mu_1',xlim=(0,6))
    ax.legend(fontsize=8)
fig.suptitle('History dependence: real-positive models at cut400 — DIAGNOSTIC_NEVER_A_PROOF')
fig.savefig(P/'history_profiles.png',dpi=160);fig.savefig(P/'history_profiles.pdf')
