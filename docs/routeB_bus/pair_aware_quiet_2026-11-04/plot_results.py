from pathlib import Path
import os,csv,json
os.environ['MPLCONFIGDIR']='/tmp/pairaware_mpl';os.environ['XDG_CACHE_HOME']='/tmp/pairaware_cache'
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent;fig,ax=plt.subplots(1,3,figsize=(13,4))
ax[0].bar(['original','θ=.5','θ=.6','θ=.75'],[14,12,12,9],color=['#6b7280','#338c91','#338c91','#338c91']);ax[0].set(ylim=(0,30),ylabel='resolved positive cells /30',title='Zeta, m310…600: admissible subset')
ax[0].axhline(30,color='#bd6658',linestyle='--',linewidth=.7)
a=[2.105038491662235,2.153837773001046,0.04879928133881073];b=[1.027817038111479,1.0673596131887715,0.03954257507729242];x=np.arange(3);ax[1].bar(x-.17,a,.34,label='q127 original',color='#6b7280');ax[1].bar(x+.17,b,.34,label='q128 pair aware',color='#338c91');ax[1].set_xticks(x,['δ','λr','gap']);ax[1].set_title('m248: residual drops, gap also drops');ax[1].legend(fontsize=8)
l2=json.loads((P/'L2_SCORE.json').read_text());v=l2['primary_L2']['coverage_given_outcome'];ax[2].bar(['observed','L2 prediction'],[100*v,70],color=['#338c91','#bd6658']);ax[2].set(ylim=(0,100),ylabel='straddling pair among flagged cells, %',title='θ=.6, frozen original winning cutoff');ax[2].text(0,100*v+3,'9 /47',ha='center')
for a in ax:a.grid(axis='y',alpha=.15)
fig.tight_layout();fig.savefig(P/'RESULT.png',dpi=160)
