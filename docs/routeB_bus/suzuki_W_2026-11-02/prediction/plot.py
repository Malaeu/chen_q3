"""Plot only the finite, registered prediction grids; never a proof."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
fig,axs=plt.subplots(2,1,figsize=(10,8),constrained_layout=True)
colors={'zeta':'#168f87','dh':'#c2574a','plant':'#68629b'}
for world in colors:
 r=list(csv.DictReader((P/f'{world}_h.025_dps80.csv').open()));axs[0].plot([float(x['t']) for x in r],[float(x['schur']) for x in r],label=world,color=colors[world],lw=1)
axs[0].set_yscale('symlog',linthresh=.002);axs[0].axhline(0,color='black',lw=.6)
for t,label in [(1.275,'Plant first negative 1.275'),(5.45,'DH first negative 5.45')]:axs[0].axvline(t,color='gray',ls=':',lw=.7);axs[0].text(t,.97,label,transform=axs[0].get_xaxis_transform(),rotation=90,va='top',ha='right',fontsize=8)
axs[0].set(title='Signed Schur innovations, h=0.025',ylabel='σ²: signed Schur defect (symlog)');axs[0].legend(loc='lower left')
for h in ('.1','.05','.025'):
 r=list(csv.DictReader((P/f'zeta_h{h}_dps80.csv').open()));axs[1].plot([float(x['t']) for x in r],[float(x['schur']) for x in r],label=f'h={h}',lw=1)
axs[1].set(title='Zeta: mesh dependence of finite Schur innovations',xlabel='New sample t (fixed preceding uniform-grid samples)',ylabel='σ²: signed Schur defect');axs[1].legend()
fig.suptitle('DIAGNOSTIC_NEVER_A_PROOF • source arithmetic • 80 decimal digits')
fig.savefig(P/'profiles.png',dpi=180);fig.savefig(P/'profiles.pdf');plt.close(fig)
