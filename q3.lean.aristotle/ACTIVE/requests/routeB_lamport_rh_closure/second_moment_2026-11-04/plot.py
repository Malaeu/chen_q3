"""Finite scalar diagnostics; no extrapolation or count-bound claim."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
s=list(csv.DictReader((P/'SUMMARY.csv').open()));fig,ax=plt.subplots(1,2,figsize=(12,4.4))
for w in ['zeta','dh','plant']:
 r=[x for x in s if x['world']==w and x['cutoff']=='primary'and x['sigma_convention']=='L_plus_inv_gamma'];ax[0].plot([int(x['m'])for x in r],[float(x['v'])for x in r],label=w)
ax[0].axhline(1,color='gray',lw=.8,ls=':');ax[0].axhline(4/3,color='gray',lw=.8,ls='--');ax[0].set(xlabel='m',ylabel='measured v',title='Primary cutoff; sigma = L + 1/gamma*');ax[0].legend()
r=[x for x in s if x['world']=='zeta'and x['cutoff']=='primary'and x['sigma_convention']=='L_plus_inv_gamma'];ms=[int(x['m'])for x in r]
ax[1].plot(ms,[float(x['raw_simple_lower'])for x in r],label='raw 2 - v (fails SANITY)');ax[1].plot(ms,[float(x['finite_unpaid_simple_score'])for x in r],label='finite trace score (unpaid)');ax[1].axhline(1,color='black',lw=.8,label='census simple fraction');ax[1].set(xlabel='m',ylabel='score',title='Zeta: raw vs finite unpaid trace score');ax[1].legend(fontsize=8)
fig.suptitle('Finite diagnostics only: count interpretation stopped for all sigma conventions',fontsize=10);fig.tight_layout();fig.savefig(P/'FINITE_DIAGNOSTICS.png',dpi=160)
