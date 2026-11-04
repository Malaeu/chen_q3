"""Display certified finite fractions on the requested grid only."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent;r=list(csv.DictReader((P/'GROWTH.csv').open()));m=[int(x['m'])for x in r]
fig,ax=plt.subplots(figsize=(8,4.4))
ax.plot(m,[float(x['s1_fraction'])for x in r],'o-',label='simple on line: original consumer')
ax.plot(m,[float(x['Nd_fraction'])for x in r],'s-',label='distinct upper zeros')
ax.plot(m,[float(x['s1_integer_refined_fraction'])for x in r],'x--',label='simple on line: integer refinement',alpha=.8)
ax.set(xlabel='m',ylabel='certified lower bound / N upper',ylim=(0,.7),title='Finite Arb bounds under explicit theorem premises')
ax.set_xticks(m);ax.grid(alpha=.2);ax.legend();fig.text(.5,.01,'DIAGNOSTIC_NEVER_A_PROOF • five cells only • no cofinal inference',ha='center',fontsize=9)
fig.tight_layout(rect=(0,.035,1,1));fig.savefig(P/'GROWTH.png',dpi=150)
