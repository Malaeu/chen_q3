"""Own-source DH point thermometer and dense corner-minor controls."""
from pathlib import Path
import numpy as np,json,csv,math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parents[1];s=json.loads((P/'ADD_DH_SUMMARY.json').read_text());v=np.memmap('/workspace/corner_thermometer/addendum/DH_Psi_n2_N.float64',dtype='<f8',mode='r');edges=np.unique(np.rint(np.exp(np.linspace(math.log(2),math.log(1e7),1801))).astype(int));edges[0]=2;edges[-1]=10000001;rs=[]
for lo,hi in zip(edges,edges[1:]):
 a=v[lo-2:hi-2]
 if not len(a):continue
 rs.append(dict(m_first=int(lo),m_last=int(hi-1),Psi_min=float(np.min(a)),Psi_max=float(np.max(a))))
with(P/'ADD_DH_ENVELOPE.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=list(rs[0]));w.writeheader();w.writerows(rs)
x=[(math.log(r['m_first'])+math.log(r['m_last']))/2 for r in rs];lo=[r['Psi_min']for r in rs];hi=[r['Psi_max']for r in rs]
fig,ax=plt.subplots(1,2,figsize=(12,4.5));ax[0].fill_between(x,lo,hi,color='#1b8c8d',alpha=.35);ax[0].plot(x,[(a+b)/2 for a,b in zip(lo,hi)],color='#17696a',lw=.7);ax[0].axhline(0,color='black',lw=.8);ax[0].set(xlabel='log m',ylabel='Psi_DH(log m)',title='Own DH source: every integer through 10,000,000')
check=json.loads((P/'ADD_DH_CHECKS.json').read_text());pts=check['direct_small_corners'];ax[0].scatter([math.log(r['m'])for r in pts],[float(r['Psi_direct60'])for r in pts],color='#bd443a',s=20,zorder=3)
for r in pts:ax[0].annotate(str(r['m']),(math.log(r['m']),float(r['Psi_direct60'])),xytext=(4,6),textcoords='offset points',fontsize=8)
d=list(csv.DictReader((P/'ADD_DH_DENSE.csv').open()));ax[1].plot([int(r['m'])for r in d],[float(r['max_rawratio'])for r in d],color='#aa493b',lw=.6);ax[1].axhline(1,color='black',lw=.8,ls='--');ax[1].set(xlabel='m',ylabel='max raw corner-minor ratio',title='DH: every m=2..2000; first crossing at 463')
for a in ax:a.grid(alpha=.2)
fig.text(.5,.01,'Point diagnostics only. Nonpositive diagonals are reported separately; the ratio alone is not a PSD criterion.',ha='center',fontsize=9);fig.tight_layout(rect=(0,.035,1,1));fig.savefig(P/'ADD_DH_DIAGNOSTICS.png',dpi=160)
