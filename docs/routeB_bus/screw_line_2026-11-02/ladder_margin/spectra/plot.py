from pathlib import Path
import csv,numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent;r=list(csv.DictReader((P/'ordering.csv').open()));c=list(csv.DictReader((P/'robustness.csv').open()))
fig,ax=plt.subplots(1,2,figsize=(12,4.8),layout='constrained');x=np.array([int(v['mesh']) for v in r])
for name,label,color in [('poisson_median','Poisson median','#c9624d'),('gue_median','GUE bulk median','#5c66ac'),('picket','Picket','#8a6a1f'),('zeta_surrogate','Zeta <=400 + common tail','#197f85'),('zeta_arithmetic','Actual arithmetic zeta','#222222')]:
 ax[0].plot(x,[float(v[name]) for v in r],'-o',label=label,color=color)
ax[0].fill_between(x,[float(v['gue_q025']) for v in r],[float(v['gue_q975']) for v in r],color='#5c66ac',alpha=.15)
ax[0].set(xlabel='mesh denominator (Delta=1/denominator)',ylabel='median one-endpoint margin, old a in [1,6]',title='Registered full ordering fails');ax[0].legend(fontsize=8)
for field,label,color in [('poisson_median','Poisson first4','#c9624d'),('gue_median','GUE first4','#5c66ac'),('picket','Picket','#8a6a1f')]:
 s=[v for v in c if int(v['mesh'])==256 and v['control']=='cutoff'];ax[1].plot([int(v['cut']) for v in s],[float(v[field]) for v in s],'-o',label=label,color=color)
ax[1].set(xlabel='discrete spectral cutoff',ylabel='primary margin statistic',title='Physical tail replacement matters (Delta=1/256)');ax[1].legend()
fig.suptitle('LADDER_AND_MARGIN spectral models — DIAGNOSTIC_NEVER_A_PROOF')
fig.savefig(P/'spectral_controls.png',dpi=160);fig.savefig(P/'spectral_controls.pdf')
