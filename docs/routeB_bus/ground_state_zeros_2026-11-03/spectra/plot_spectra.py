from pathlib import Path
import csv,math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'spectra.csv').open()))
fig,axs=plt.subplots(1,3,figsize=(15,4.3))
for ax,w in zip(axs,['zeta','dh','plant']):
 rr=sorted([a for a in rows if a['world']==w],key=lambda x:int(x['m']));mm=[int(a['m']) for a in rr]
 if w=='zeta':
  # Parse signed scientific strings without underflowing very small positive eigenvalues.
  def lg(s):
   from decimal import Decimal
   x=abs(Decimal(s));return float(x.log10()) if x else float('nan')
  ax.plot(mm,[lg(a['lambda_even0']) for a in rr],label='even λ0');ax.plot(mm,[lg(a['lambda_odd0']) for a in rr],label='odd λ0');ax.plot(mm,[lg(a['global_gap']) for a in rr],label='global gap',linestyle='--');ax.set_ylabel('log₁₀ magnitude')
 else:
  ax.plot(mm,[float(a['lambda_even0']) for a in rr],label='even λ0');ax.plot(mm,[float(a['lambda_odd0']) for a in rr],label='odd λ0');ax.axhline(0,color='0.6',linewidth=.6);ax.set_ylabel('λ0')
 ax.set_title(w);ax.set_xlabel('m');ax.grid(alpha=.2);ax.legend(fontsize=8)
fig.suptitle('Literal CCM ground spectra: complete source, both parity blocks',fontsize=12);fig.tight_layout();fig.savefig(P/'spectra.png',dpi=180);fig.savefig(P/'spectra.svg')
