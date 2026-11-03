"""Plot retained extension-margin measurements; no new eigenproblems."""
from pathlib import Path
import os,json,csv
os.environ.setdefault('MPLCONFIGDIR','/tmp/extension-matplotlib')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
def read(path):return list(csv.DictReader(path.open()))
fig,axs=plt.subplots(2,2,figsize=(12,8),layout='constrained')
rows=read(P/'uniform'/'single_endpoint.csv')
for mesh in [32,64,128,256]:
 r=[x for x in rows if x['world']=='zeta' and int(x['mesh'])==mesh]
 axs[0,0].plot([float(x['a']) for x in r],[float(x['mu']) for x in r],label=f'1/{mesh}')
axs[0,0].set(title='Zeta: one-point margin, delta=Delta',xlabel='old history length a',ylabel='mu_1');axs[0,0].legend(title='Delta')
summary=json.loads((P/'uniform'/'SUMMARY.json').read_text())
for r in summary['a6_refinement']:
 qs=[1,4,8,16,32,64,128];axs[0,1].plot(qs,[r[f'q{q}'] for q in qs],marker='.',label=f"1/{r['mesh']}")
axs[0,1].axhline(.1,color='black',ls='--',lw=.8);axs[0,1].set_xscale('log',base=2)
axs[0,1].set(title='Fresh-node refinement at a=6, delta=Delta',xlabel='number q of fresh nodes',ylabel='finite margin mu_q');axs[0,1].legend(title='Delta')
rows=read(P/'uniform'/'nested_step_search.csv')
for mesh in [32,64,128,256]:
 r=[x for x in rows if int(x['mesh'])==mesh and float(x['a'])==6]
 axs[1,0].loglog([float(x['delta']) for x in r],[float(x['mu']) for x in r],marker='.',label=f'1/{mesh}')
axs[1,0].set(title='Nested fresh grid: no failure to search cap 1/4',xlabel='tested extension delta',ylabel='mu_q (sampled, not all-node)');axs[1,0].legend(title='Delta')
rows=read(P/'uniform'/'future_refinement.csv')
for world,color in [('dh','#d66b53'),('plant','#79539d')]:
 for q,style in [(1,'-'),(32,'--')]:
  r=sorted([x for x in rows if x['world']==world and int(x['mesh'])==256 and int(x['q'])==q and x['mu']],key=lambda x:float(x['a']))
  axs[1,1].plot([float(x['a']) for x in r],[float(x['mu']) for x in r],style,marker='.',color=color,label=f'{world}, q={q}')
axs[1,1].axhline(0,color='black',lw=.8);axs[1,1].set_yscale('symlog',linthresh=.1)
axs[1,1].set(title='Broken worlds: valid pasts only, Delta=1/256',xlabel='old history length a',ylabel='signed margin');axs[1,1].legend()
fig.suptitle('EXTENSION_MARGIN_v1 — DIAGNOSTIC_NEVER_A_PROOF',fontsize=14)
fig.savefig(P/'profiles.png',dpi=160);fig.savefig(P/'profiles.pdf')
plt.close(fig)
fig,axs=plt.subplots(1,2,figsize=(12,4),layout='constrained')
single=read(P/'sections'/'all_sections_q1.csv');multi=read(P/'sections'/'representative_q_refinement.csv')
for mesh in [32,64,128,256]:
 r=[x for x in single if x['world']=='zeta' and int(x['mesh'])==mesh and x['mu']]
 axs[0].plot([int(x['n']) for x in r],[float(x['mu']) for x in r],label=f'1/{mesh}')
 r=[x for x in multi if x['world']=='zeta' and int(x['mesh'])==mesh and int(x['n'])==16 and x['mu']]
 axs[1].loglog([int(x['q']) for x in r],[float(x['mu']) for x in r],marker='.',label=f'1/{mesh}')
for ax in axs:ax.axhline(.1,color='black',ls='--',lw=.8);ax.legend(title='old mesh Delta')
axs[0].set(title='All zeta arithmetic sections, one new endpoint',xlabel='section n (old endpoint log n)',ylabel='mu_1')
axs[1].set(title='Section16: refine future and old history',xlabel='number q of fresh nodes',ylabel='mu_q (finite upper approximant)')
fig.suptitle('Arithmetic-section floor 0.1 fails numerically — DIAGNOSTIC_NEVER_A_PROOF')
fig.savefig(P/'sections.png',dpi=160);fig.savefig(P/'sections.pdf')
