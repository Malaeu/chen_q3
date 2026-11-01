"""Plot physical densities from the computed samples; no inference from plotting."""
from pathlib import Path
import argparse,csv,os
os.environ.setdefault("MPLCONFIGDIR","/tmp/lowcluster-matplotlib")
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'shape_samples.csv').open()))
fig,axs=plt.subplots(1,2,figsize=(11,4),constrained_layout=True)
colors=['#147d92','#d16b47','#558342','#85569a']
for m,color in zip((12,16,20,24),colors):
 r=[x for x in rows if int(x['m'])==m];xs=[float(x['x']) for x in r]
 axs[0].plot(xs,[float(x['f']) for x in r],label=f'm={m}',color=color,lw=1.6)
 axs[1].plot(xs,[float(x['density']) for x in r],label=f'm={m}',color=color,lw=1.6)
for ax in axs:
 ax.set_xlim(-1.65,1.65);ax.set_xlabel('Physical x');ax.grid(alpha=.2);ax.legend(frameon=False)
axs[0].set_ylabel('Unit L2-normalized function');axs[1].set_ylabel('Probability density |f(x)|²')
axs[0].set_title('Direction least aligned with the six-profile ladder')
axs[1].set_title('Peaks remain near x = ±0.98')
fig.suptitle('Finite CCM canary: zero extension outside each window',fontsize=11)
fig.savefig(P/'physical_profiles.svg')
p=argparse.ArgumentParser();p.add_argument('--png');a=p.parse_args()
if a.png:fig.savefig(a.png,dpi=160)
# Physical cross-Gram matrices, with a fixed color scale across consecutive pairs.
import numpy as np
rr=list(csv.DictReader((P/'physical_gram_consecutive.csv').open()))
fig2,axes=plt.subplots(1,3,figsize=(11,3.6),constrained_layout=True)
for ax,(m,n) in zip(axes,((12,16),(16,20),(20,24))):
 C=np.zeros((8,8))
 for r in rr:
  if int(r['m'])==m and int(r['m_prime'])==n:C[int(r['i']),int(r['j'])]=float(r['absolute_inner'])
 im=ax.imshow(C,vmin=0,vmax=1,cmap='viridis',origin='upper')
 ax.set_title(f'm={m} → {n}');ax.set_xlabel(f'Level j at m={n}');ax.set_ylabel(f'Level i at m={m}')
 ax.set_xticks(range(8));ax.set_yticks(range(8))
fig2.colorbar(im,ax=axes,label='Absolute physical overlap',shrink=.8)
fig2.savefig(P/'overlap_matrices.svg')
