"""Plot observed level assignments; diagnostic only."""
from pathlib import Path
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'matches.csv').open()))
colors={16:'#087f8c',24:'#d16b48',32:'#6c58a0',40:'#467a37'}
fig,axs=plt.subplots(2,3,figsize=(14,8),constrained_layout=True)
for col,B in enumerate((2,4,8)):
 for m in colors:
  r=[x for x in rows if int(x['m'])==m and int(x['B'])==B and x['method']=='ordinal']
  axs[0,col].plot([float(x['x']) for x in r],[float(x['log_lambda']) for x in r],'.-',label=f'm={m}',color=colors[m],lw=1)
  axs[1,col].plot([float(x['x']) for x in r],[max(float(x['distance_over_local_spacing']),1e-16) for x in r],'.-',color=colors[m],lw=1)
  st=[x for x in r if x['root_kind']=='structural_exterior']
  axs[1,col].scatter([float(x['x']) for x in st],[float(x['distance_over_local_spacing']) for x in st],marker='x',color=colors[m],s=70,zorder=5)
 axs[0,col].set_title(f'Cluster threshold m⁻{B}; ordinal matching')
 axs[0,col].set_ylabel('ln λ');axs[0,col].legend(fontsize=8)
 axs[1,col].set_ylabel('Nearest Fourier-root distance / local ζ spacing')
 axs[1,col].set_yscale('log')
 for ax in axs[:,col]:
  ax.set_xlabel('x = γⱼ / (2πm / ln m)');ax.grid(alpha=.2);ax.axvline(1,color='#777777',ls=':',lw=1)
fig.suptitle('Literal even CCM: level–zero ladder test\nDIAGNOSTIC_NEVER_A_PROOF · crosses mark forced exterior modal zeros',fontsize=13)
fig.savefig(P/'level_zero_ladder.svg');fig.savefig(P/'level_zero_ladder.png',dpi=160);plt.close(fig)
fig,axs=plt.subplots(1,4,figsize=(15,4),constrained_layout=True)
cost=list(csv.DictReader((P/'matching_costs.csv').open()))
for ax,m in zip(axs,colors):
 r=[x for x in cost if int(x['m'])==m and int(x['B'])==2]
 ids=sorted(set(int(x['i']) for x in r));q=len(ids);a=np.zeros((q,q))
 for x in r:a[ids.index(int(x['i'])),int(x['j'])-1]=max(float(x['distance_over_local_spacing']),1e-16)
 im=ax.imshow(np.log10(a),origin='lower',aspect='auto',cmap='viridis',vmin=-5,vmax=0)
 ax.set_title(f'm={m}, lifted levels={q}');ax.set_xlabel('zeta index j (1-based)');ax.set_ylabel('lifted rank (1-based)')
 ticks=np.unique(np.linspace(0,q-1,min(q,5),dtype=int));ax.set_xticks(ticks,ticks+1);ax.set_yticks(ticks,ticks+1)
 fig.colorbar(im,ax=ax,label='log₁₀(distance / spacing)',shrink=.8)
fig.suptitle('All-pairs Fourier-root distances, B=2: test for a distinguished diagonal')
fig.savefig(P/'root_matching_costs.svg');plt.close(fig)
fig,axs=plt.subplots(1,3,figsize=(14,4),constrained_layout=True)
for ax,method,title in zip(axs,('ordinal','root_bijective','root_independent'),('Ordinal','Forced one-to-one root match','Independent closest-root match')):
 for m in colors:
  r=sorted([x for x in rows if int(x['m'])==m and x['B']=='2' and x['method']==method],key=lambda x:int(x['j']))
  ax.plot([float(x['x']) for x in r],[float(x['log_lambda']) for x in r],'.-',label=f'm={m}',color=colors[m],lw=1)
 ax.set_title(title);ax.set_xlabel('x = γⱼ / (2πm / ln m)');ax.set_ylabel('ln λ');ax.grid(alpha=.2);ax.legend(fontsize=8)
fig.suptitle('B=2: alternative assignments change the energy curves (diagnostic only)')
fig.savefig(P/'alternative_assignments.svg');plt.close(fig)
