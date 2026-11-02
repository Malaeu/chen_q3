"""Plot saved measurements only; no new eigenproblems."""
from pathlib import Path
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
def read(p):return list(csv.DictReader(p.open()))
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,ax=plt.subplots(2,2,figsize=(12,8),layout='constrained')
for mesh in [32,64,128,256]:
    data=read(P/'core'/f'zeta_mesh{mesh}_dps100.csv')
    t=np.array([float(r['t']) for r in data]); y=np.array([float(r['sigma2']) for r in data])
    ax[0,0].semilogy(t,y,label=f'1/{mesh}')
    ax[0,1].plot(t,y/y[0],label=f'1/{mesh}')
ax[0,0].set(title='Zeta: innovations stay positive through t=6',xlabel='history length t',ylabel='sigma² (log scale)')
ax[0,0].legend(title='mesh Δ')
ax[0,1].set(title='Local-cusp normalization does not collapse the curves',xlabel='history length t',ylabel='sigma² / (2 Psi(Δ))')
ax[0,1].legend(title='mesh Δ')
for world,color in [('zeta','#117e83'),('dh','#dd7057'),('plant','#7559a7')]:
    data=read(P/'core'/f'{world}_mesh256_dps100.csv')
    t=[float(r['t']) for r in data]; ni=[int(r['negative_inertia']) for r in data]
    ax[1,0].step(t,ni,where='post',label=world,color=color)
ax[1,0].set(title='Nested negative index retains every failure (Δ=1/256)',xlabel='history length t',ylabel='number of negative pivots')
ax[1,0].legend()
for mesh in [32,64,128,256]:
    data=read(P/'review'/f'plant_hazard_mesh{mesh}.csv')
    # Schema is fixed by the independent low-rank experiment.
    xkey='t'; ykey=next(k for k in data[0] if k in ('theta_max','theta_eigen_max'))
    ax[1,1].semilogy([float(r[xkey]) for r in data],[max(1e-8,float(r[ykey])) for r in data],label=f'1/{mesh}')
ax[1,1].axhline(1,color='black',ls='--',lw=1)
ax[1,1].set(title='Planted quartet: monotone 2×2 hazard crosses 1',xlabel='history length t',ylabel='largest eigenvalue of Θ')
ax[1,1].legend(title='mesh Δ')
fig.suptitle('INNOVATION_LAW_v1 — DIAGNOSTIC_NEVER_A_PROOF',fontsize=14)
fig.savefig(P/'profiles.png',dpi=160);fig.savefig(P/'profiles.pdf')
plt.close(fig)

fig,ax=plt.subplots(1,2,figsize=(12,4),layout='constrained')
data=read(P/'residual'/'profiles.csv')
for t in ['1.0','3.0','6.0']:
    rows=[r for r in data if r['world']=='zeta' and r['mesh']=='64' and r['t']==t]
    ax[0].step([float(r['x_left']) for r in rows]+[float(t)],[float(r['f']) for r in rows]+[float(rows[-1]['f'])],where='post',label=f't={t}')
ax[0].set(title='Optimal zeta step residual occupies the history',xlabel='physical x',ylabel='f*(x), terminal value = 1');ax[0].legend()
rows=[r for r in read(P/'residual'/'budgets.csv') if r['world']=='zeta' and r['mesh']=='64' and r['t']=='6.0']
r=rows[0];keys=['arch','constant','pole','arithmetic','sigma2'];vals=[float(r[k]) for k in keys]
ax[1].bar(keys,vals,color=['#117e83' if v>=0 else '#dd7057' for v in vals]);ax[1].axhline(0,color='black',lw=.7)
ax[1].set(title='Full source cancellation at t=6, Δ=1/64',ylabel='signed contribution')
ax[1].annotate(f"sum = {vals[-1]:.8f}",(4,vals[-1]),xytext=(3,12),arrowprops={'arrowstyle':'->'})
fig.suptitle('DIAGNOSTIC_NEVER_A_PROOF',fontsize=13)
fig.savefig(P/'residuals.png',dpi=160);fig.savefig(P/'residuals.pdf')
