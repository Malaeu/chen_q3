"""Plot finite phase-space V diagnostics, without asymptotic inference."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
def rows(n):return list(csv.DictReader((P/n).open()))
res=rows('resolution_main.csv');sh=rows('shake_summary.csv');base=rows('literal_baselines.csv');cl=rows('cluster_main.csv')
fig,ax=plt.subplots(1,3,figsize=(14,4.2),layout='constrained')
for m,color in [(8,'#187f80'),(12,'#d36b56'),(16,'#576bb1')]:
    r=[x for x in res if int(x['window_m'])==m]
    ax[0].plot([int(x['N']) for x in r],[float(x['V']) for x in r],'o-',label=f'L=log {m}',color=color)
ax[0].set_title('True source, fixed-window resolution');ax[0].set_xlabel('N');ax[0].set_ylabel('V');ax[0].legend(fontsize=8)
ax[1].plot([int(x['m']) for x in base],[float(x['V']) for x in base],'ko-',label='true source')
for eps in ('1e-26','1e-20','1e-12','1e-6'):
    r=[x for x in sh if x['epsilon']==eps and x['convention']=='analytic_continuation']
    ax[1].plot([int(x['m']) for x in r],[float(x['V']) for x in r],'o-',label=eps)
ax[1].set_title('Positive SHAKE: formula as referenced');ax[1].set_xlabel('m = N');ax[1].set_ylabel('V');ax[1].legend(fontsize=7)
ii=[int(x['i']) for x in cl];aa=[float(x['arch']) for x in cl];xx=[float(x['spatial']) for x in cl]
ax[2].bar(ii,aa,color='#187f80',label='archimedean');ax[2].bar(ii,xx,bottom=aa,color='#d36b56',label='spatial')
ax[2].set_title('m=24 near-null levels');ax[2].set_xlabel('even level i');ax[2].set_ylabel('V = arch + spatial');ax[2].set_xticks(ii);ax[2].legend(fontsize=8)
for a in ax:a.grid(axis='y',alpha=.2)
fig.suptitle('DIAGNOSTIC_NEVER_A_PROOF',fontsize=11)
fig.savefig(P/'phase_space_V.svg')
