from pathlib import Path
import csv,math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
r=[x for x in csv.DictReader((P/'spectrum.csv').open()) if int(x['m'])>=20]
fig,ax=plt.subplots(figsize=(9,4.6),layout='constrained')
for negative,color,label in [(False,'#147d92','Positive minimum'),(True,'#d45a45','Negative minimum')]:
 a=[x for x in r if (float(x['preferred_minimum_lambda'])<0)==negative]
 ax.scatter([int(x['m']) for x in a],[abs(float(x['preferred_minimum_lambda'])) for x in a],s=21,color=color,label=label)
ax.set_yscale('log');ax.set_xlabel('Literal m (N=m, L=log m)');ax.set_ylabel('Absolute value of minimum eigenvalue')
ax.axvline(51,color='#d45a45',alpha=.6,ls=':',label='First negative: m=51')
ax.axvline(55,color='#777777',alpha=.6,ls='--',label='Window frequency crosses 85.699: m=55')
ax.set_title('Davenport–Heilbronn fake-world scan — diagnostic, never a proof');ax.grid(alpha=.18);ax.legend(fontsize=9,loc='lower right')
fig.savefig(P/'minimum_scan.png',dpi=160);fig.savefig(P/'minimum_scan.svg')
