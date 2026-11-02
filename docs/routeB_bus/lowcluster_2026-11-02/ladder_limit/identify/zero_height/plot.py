"""Plot the requested global-maximum-normalized zero residuals."""
from pathlib import Path
import csv,math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
r=list(csv.DictReader((P/'samples.csv').open()))
names=[f'phi{i}' for i in range(8)]+['least_ladder']
fig,axs=plt.subplots(1,3,figsize=(14,4.5),sharey=True,layout='constrained')
for ax,m in zip(axs,[16,20,24]):
    for j,name in enumerate(names):
        rr=[x for x in r if int(x['m'])==m and x['profile']==name]
        ax.semilogy([float(x['gamma']) for x in rr],[float(x['normalized_absolute']) for x in rr],
                    '.-',ms=2,lw=.8,label=name,color=plt.get_cmap('tab10')(j))
    ax.axhline(1e-6,color='#9b3131',ls='--',lw=.8)
    ax.axhline(1e-3,color='#333333',ls=':',lw=.8)
    ax.axvline(2*math.pi*m/math.log(m),color='#555555',ls='--',lw=.9,label='carrier endpoint')
    ax.axvline(2*math.pi*m,color='#555555',ls=':',lw=.9,label='CC comparison scale')
    ax.set_title(f'm = N = {m}');ax.set_xlabel('zeta-zero height');ax.set_xlim(0,300);ax.grid(alpha=.15)
axs[0].set_ylabel('|Phi(gamma)| / max |Phi|');axs[0].set_ylim(1e-55,1e-2)
axs[-1].legend(fontsize=7,loc='lower right',ncol=2)
fig.suptitle('DIAGNOSTIC_NEVER_A_PROOF — absolute residual thresholds, not zero-location errors',fontsize=10)
fig.savefig(P/'zero_height.svg')
