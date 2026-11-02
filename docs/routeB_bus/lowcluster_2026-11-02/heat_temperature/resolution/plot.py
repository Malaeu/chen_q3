"""Compare literal and fixed-window heat temperatures; finite diagnostics only."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
r=list(csv.DictReader((P/'main_fits.csv').open()))
literal=list(csv.DictReader((P.parent/'fits.csv').open()))
fig,ax=plt.subplots(1,2,figsize=(10,3.8),layout='constrained')
for m,color in [(8,'#187f80'),(12,'#d36b56')]:
    lo=next(x for x in literal if int(x['m'])==m and x['family']=='heat')
    rr=[x for x in r if int(x['window_m'])==m]
    ns=[m]+[int(x['N']) for x in rr]
    ss=[float(lo['s'])]+[float(x['s_star']) for x in rr]
    residuals=[float(lo['residual_squared'])]+[float(x['residual_squared']) for x in rr]
    ax[0].plot(ns,ss,'o-',color=color,label=f'L = log {m}')
    ax[1].plot(ns,residuals,'o-',color=color,label=f'L = log {m}')
ax[0].set_title('Best-found forward heat time');ax[0].set_ylabel('s* (constrained to s >= 0)')
ax[1].set_title('Squared L2 residual at the fitted time')
for a in ax:a.set_xlabel('N, at fixed L');a.set_xticks([8,12,44,56,68]);a.grid(alpha=.2);a.legend()
fig.suptitle('DIAGNOSTIC_NEVER_A_PROOF — eigenvalues are not yet N-converged',fontsize=10)
fig.savefig(P/'resolution.svg')
