"""Plot retained same-ambient B metrics only; no new numerical experiment."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent;r=list(csv.DictReader((P/'preferred.csv').open()));fig,ax=plt.subplots(1,2,figsize=(11.5,4.4),layout='constrained')
for world,label,color in [('zeta','Zeta','#187e84'),('dh','DH (coarse positive cells)','#ca6752'),('plant','Plant (stationary residual)','#7561a9')]:
 s=sorted([v for v in r if v['world']==world and v['cutoff']=='cquarter'],key=lambda v:int(v['m']));x=[int(v['m']) for v in s]
 ax[0].plot(x,[float(v['angle_f_J_degrees']) for v in s],'-o',label=label,color=color)
 ax[1].semilogy(x,[float(v['delta_full_AQ']) for v in s],'-o',label=label,color=color)
ax[0].set(xlabel='m',ylabel='one-direction angle(f,J), degrees',title='Primary c=1/4: same physical L2 geometry');ax[0].legend(fontsize=8)
ax[1].axhline(2,color='black',ls='--',lw=1,label='threshold 2');ax[1].set(xlabel='m',ylabel='full operator residual ||A Q||',title='A small angle does not supply a quiet-space budget');ax[1].legend(fontsize=8)
fig.suptitle('B_stitch — DIAGNOSTIC_NEVER_A_PROOF')
fig.savefig(P/'profiles.png',dpi=160);fig.savefig(P/'profiles.pdf')
