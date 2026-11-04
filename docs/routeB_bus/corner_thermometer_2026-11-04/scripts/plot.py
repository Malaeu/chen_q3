"""Plot all-integer coverage through logarithmic min/max envelopes."""
from pathlib import Path
import csv,json,math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parents[1];rs=list(csv.DictReader((P/'LOG_ENVELOPE.csv').open()));s=json.loads((P/'NATIVE_SUMMARY.json').read_text())
x=[(math.log(int(r['m_first']))+math.log(int(r['m_last'])))/2 for r in rs];lo=[float(r['Psi_min'])for r in rs];hi=[float(r['Psi_max'])for r in rs]
fig,ax=plt.subplots(figsize=(12,4.8));ax.fill_between(x,lo,hi,color='#208d8e',alpha=.35,label='min/max in 4000 uniform log bins');ax.plot(x,[(a+b)/2 for a,b in zip(lo,hi)],color='#17696a',lw=.7)
ax.axhline(float(s['mean_uniform_t_continuous']),color='#d66a51',ls='--',lw=1,label='continuous uniform-t mean');ax.axhline(0,color='black',lw=.6)
ax.scatter([math.log(s['minimum_m']),math.log(s['maximum_m'])],[float(s['minimum']),float(s['maximum'])],color='#ac382d',s=24,zorder=3,label='native global extrema')
ax.set(xlabel='log m',ylabel='Psi(log m)',xlim=(math.log(2),math.log(1e8)),title='Corner thermometer: every integer 2 through 100,000,000');ax.legend(loc='upper left',fontsize=8);ax.grid(alpha=.2)
fig.text(.5,.01,'Compensated long-double point scan; 40dps checkpoints and local refinement. Diagnostic, never a proof.',ha='center',fontsize=9);fig.tight_layout(rect=(0,.03,1,1));fig.savefig(P/'PSI_LOG_M.png',dpi=160)
