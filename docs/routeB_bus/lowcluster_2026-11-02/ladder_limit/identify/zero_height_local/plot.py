"""Local Fourier-envelope residuals, including controls; finite diagnostic."""
from pathlib import Path
import csv,math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
fig,axs=plt.subplots(1,3,figsize=(14,4.7),sharey=True,layout='constrained')
for ax,m in zip(axs,[16,20,24]):
    rows=list(csv.DictReader((P/f'samples_m{m}.csv').open()))
    for i in list(range(8))+[m//2,m-2]:
        r=[x for x in rows if int(x['i'])==i]
        color=plt.get_cmap('tab10')(i) if i<8 else ('black' if i==m//2 else '#994b0b')
        style='-' if i<8 else ('--' if i==m//2 else '-.')
        label=f'phi{i}' if i<8 else ('control m/2' if i==m//2 else 'control m-2')
        ax.semilogy([float(x['gamma']) for x in r],[float(x['rho']) for x in r],style,lw=.9,color=color,label=label)
    ax.axhline(1e-6,color='#d14a4a',ls=':',lw=1)
    ax.axhline(1e-2,color='#d14a4a',ls='--',lw=1)
    ax.axvline(2*math.pi*m/math.log(m),color='#777777',ls='--',lw=.9)
    ax.axvline(2*math.pi*m,color='#777777',ls=':',lw=.9)
    ax.set_title(f'm = N = {m}');ax.set_xlim(0,300);ax.set_xlabel('zeta-zero height');ax.grid(alpha=.15)
axs[0].set_ylim(1e-55,1.5);axs[0].set_ylabel('local residual rho')
axs[-1].legend(ncol=2,fontsize=7,loc='lower right')
fig.suptitle('DIAGNOSTIC_NEVER_A_PROOF — vertical dashed: 2 pi m/log m; dotted: 2 pi m',fontsize=10)
fig.savefig(P/'local_zero_height.svg')
