"""Plot the finite heat fits; no mathematical inference from plotted trends."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'fits.csv').open()))
fig,ax=plt.subplots(1,3,figsize=(12,3.5),layout='constrained')
for family,label,color in [('heat','Full heat','#187f80'),('quadratic','Second-order family','#d36b56')]:
    r=[x for x in rows if x['family']==family];m=[int(x['m']) for x in r]
    ax[0].plot(m,[float(x['s']) for x in r],'o-',label=label,color=color)
    ax[1].semilogy(m,[float(x['residual_squared']) for x in r],'o-',color=color)
    ax[2].semilogy(m,[float(x['energy_over_lambda0']) for x in r],'o-',color=color)
for a,title in zip(ax,['Fitted forward-heat time','Squared L2 fit residual','Rayleigh quotient / ground eigenvalue']):
    a.set_title(title,fontsize=10);a.set_xlabel('m = N');a.set_xticks([8,12,16,20,24]);a.grid(alpha=.2)
ax[0].legend(fontsize=8)
fig.suptitle('DIAGNOSTIC_NEVER_A_PROOF',fontsize=11)
fig.savefig(P/'heat_temperature.svg')
