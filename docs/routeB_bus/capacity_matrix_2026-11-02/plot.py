"""Spectrum and prefix convergence visualization; no float64 eigensolver."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
fig,axs=plt.subplots(3,2,figsize=(12,11),constrained_layout=True)
for col,m in enumerate((16,24)):
 r=json.loads((P/f'cell_m{m}.json').read_text());a=np.array(list(map(float,r['A_eigenvalues'])));g=np.array(list(map(float,r['G_eigenvalues'])));ids=np.arange(m+1)
 axs[0,col].semilogy(ids,a,'o-',label='A_m',color='#087f8c',lw=1,ms=4)
 axs[0,col].semilogy(ids,2*g,'x--',label='2 E*E, T=400',color='#d16b48',lw=1,ms=4)
 axs[0,col].semilogy(ids,g,':',label='E*E, T=400',color='#777777',lw=1)
 axs[0,col].set(title=f'm={m}: full carrier spectrum',xlabel='Increasing eigenvalue index i',ylabel='Eigenvalue');axs[0,col].legend()
 axs[1,col].plot(ids,2*g/a,'o-',color='#d16b48',ms=4);axs[1,col].axhline(1,color='#777777',ls=':');axs[1,col].set(xlabel='Index i',ylabel='2 g_i(400) / λ_i(A)',ylim=(0,1.05))
 q=[x['q'] for x in r['prefixes'] if x['q']>=m+1];p=[x for x in r['prefixes'] if x['q']>=m+1]
 for i,label in [(0,'bottom'),(m,'top')]:
  axs[2,col].plot(q,[2*float(x['g_eigenvalues'][i])/a[i] for x in p],'.-',label=label,lw=1)
 axs[2,col].axhline(1,color='#777777',ls=':');axs[2,col].set(xlabel='Number q of positive zeros retained',ylabel='2 g_i(q) / λ_i(A)',ylim=(0,1.05));axs[2,col].legend()
 for ax in axs[:,col]:ax.grid(alpha=.2)
fig.suptitle('Capacity matrix versus literal even CCM · 180 dps · DIAGNOSTIC_NEVER_A_PROOF')
fig.savefig(P/'spectrum_convergence.svg');fig.savefig(P/'spectrum_convergence.png',dpi=150)
