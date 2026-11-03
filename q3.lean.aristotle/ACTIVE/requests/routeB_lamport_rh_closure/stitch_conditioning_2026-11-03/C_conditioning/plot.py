"""Standalone finite diagnostic, excludes unresolved values."""
import csv,math
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'conditioning.csv').open()));fig,axes=plt.subplots(2,1,figsize=(9,7),sharex=True)
for world,color in [('zeta','#087f8c'),('plant','#e76f51'),('dh','#69717d')]:
 rr=sorted([r for r in rows if r['world']==world and r['cut']=='c_quarter'],key=lambda r:int(r['m']))
 valid=[r for r in rr if r['sigma_min_squared']];axes[0].plot([int(r['m'])for r in valid],[math.log10(float(r['sigma_min_squared']))for r in valid],label=world+' raw σ²',color=color)
 axes[1].plot([int(r['m'])for r in rr],[float(r['min_included_normalized_gap'])for r in rr],label=world,color=color)
axes[0].set_ylabel('log₁₀ raw σmin²');axes[1].set_ylabel('Minimum included gap · L/(2π)');axes[1].set_xlabel('Literal m (N=m)');axes[0].legend();axes[1].legend();axes[0].set_title('Primary c=1/4, finite conditioning: DIAGNOSTIC_NEVER_A_PROOF')
for a in axes:a.grid(alpha=.2);a.axvline(65,color='#69717d',ls=':',lw=.8)
axes[1].axhline(.3,color='#69717d',ls='--',lw=.8);fig.tight_layout();fig.savefig(P/'conditioning_primary.svg');fig.savefig(P/'conditioning_primary.png',dpi=160)
