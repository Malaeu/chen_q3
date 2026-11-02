from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'scan.csv').open()));wins=list(csv.DictReader((P/'windows.csv').open()))
fig,axs=plt.subplots(2,4,figsize=(16,8),constrained_layout=True)
for col,m in enumerate((16,24,32,40)):
 r=[x for x in rows if int(x['m'])==m];x=[float(a['kappa']) for a in r]
 ax=axs[0,col];ax.semilogy(x,[float(a['delta']) for a in r],'.-',color='#087f8c',label='full ||AQ||')
 ax.semilogy(x,[float(a['beta']) for a in r],'.-',color='#d16b48',label='compressed ||Q*AQ||')
 for B,color in ((2,'#6c58a0'),(4,'#467a37')):
  ax.axhline(m**-B,color=color,ls='--',label=f'μ=m⁻{B}')
  w=next(w for w in wins if int(w['m'])==m and int(w['B'])==B);ax.axvspan(float(w['count_equality_kappa_left']),float(w['count_equality_kappa_right']),color=color,alpha=.10)
 ax.set(title=f'm={m}',ylabel='Operator norms',xlim=(1,1.4));ax.legend(fontsize=7);ax.grid(alpha=.2)
 ax=axs[1,col];ax.step(x,[int(a['dimension']) for a in r],where='post',color='#087f8c',label='dim J (sampled grid)')
 ax.plot(x,[float(a['asymptotic_dimension']) for a in r],color='#d16b48',ls=':',label='smooth approximation')
 for B,color in ((2,'#6c58a0'),(4,'#467a37')):ax.axhline(int(r[0][f'signed_count_B{B}']),color=color,ls='--',label=f'N_A(m⁻{B})')
 ax.set(xlabel='κ',ylabel='Dimension / signed count',xlim=(1,1.4));ax.legend(fontsize=7);ax.grid(alpha=.2)
fig.suptitle('Interpolation quiet spaces · shaded bands: count equality · no simultaneous residual/count window\nDIAGNOSTIC_NEVER_A_PROOF')
fig.savefig(P/'quiet_space_scan.svg');fig.savefig(P/'quiet_space_scan.png',dpi=150)
