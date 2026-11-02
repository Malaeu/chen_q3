"""Export finite diagnostic plots; no interpolation interpreted as proof."""
from pathlib import Path
import json,os
os.environ.setdefault("MPLCONFIGDIR","/tmp/screw_line_mpl")
os.environ.setdefault("XDG_CACHE_HOME","/tmp/screw_line_cache")
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
TEAL='#008b8b';CORAL='#d8624f';GRAY='#777777'
plt.rcParams.update({'font.size':10,'axes.grid':True,'grid.alpha':.2})
base=[json.loads(f.read_text()) for f in (P/'native_cells').glob('*_dps220_gl256.json')]
fig,ax=plt.subplots(3,1,figsize=(9,9),sharex=True,constrained_layout=True)
for world,color in [('zeta',TEAL),('dh',CORAL)]:
 a=sorted([d for d in base if d['world']==world],key=lambda d:d['m']);ms=[d['m'] for d in a]
 ax[0].plot(ms,[float(d['K'][0]) for d in a],label=world,color=color,lw=1.4)
 ax[1].step(ms,[d['negative_pivots'] for d in a],where='mid',label=world,color=color)
 ax[2].plot(ms,[np.sign(float(d['signed_reciprocal_proxy'][0])) for d in a],label=world,color=color,lw=1,marker='.',ms=2)
ax[0].set_ylabel('Endpoint inverse form K(b,b)');ax[0].legend()
ax[1].set_ylabel('Native negative inertia')
ax[2].set_ylabel('Sign of rho(i/2), not radius');ax[2].set_ylim(-1.25,1.25);ax[2].set_yticks([-1,0,1]);ax[2].annotate('DH m=52',xy=(52,-1),xytext=(70,-.6),arrowprops={'arrowstyle':'->','color':GRAY});ax[2].set_xlabel('m; changing order, window and native constraints')
ax[0].set_title('DIAGNOSTIC_NEVER_A_PROOF — inverse forms are not identified Weyl radii')
fig.savefig(P/'native_diagnostics.png',dpi=160);plt.close(fig)
fig,ax=plt.subplots(3,1,figsize=(9,9),constrained_layout=True)
for world,color in [('zeta',TEAL),('dh',CORAL)]:
 name='curve_zeta.json' if world=='zeta' else 'curve_refined_dh.json';d=json.loads((P/name).read_text());a=d['prefixes'];ls=np.array([float(x['L']) for x in a]);E=np.array([float(x['projection_energy']) for x in a]);inc=np.array([float(x['increment']) for x in a]);idx=0 if world=='zeta' else 1
 ax[idx].plot(ls,E,color=color,lw=1,label=f'{world}: {d["nodes"]} fixed nested nodes')
 neg=inc<0;ax[idx].scatter(ls[neg],E[neg],marker='x',s=30,color='black',label='negative increment' if neg.any() else None)
 ax[idx].set_ylabel('Projection inverse form E');ax[idx].legend();ax[idx].set_xlabel('segment length L')
for file,color,label in [('curve_dh.json',GRAY,'DH uniform240'),('curve_refined_dh.json',CORAL,'DH uniform480')]:
 d=json.loads((P/file).read_text());ax[2].step([float(x['L']) for x in d['prefixes']],[x['negative_inertia'] for x in d['prefixes']],where='post',color=color,label=label)
d=json.loads((P/'aligned_mesh_dh.json').read_text());ax[2].step([x['L'] for x in d['rows']],[x['negative_inertia'] for x in d['rows']],where='post',color=TEAL,label='DH endpoint+mesh float control')
ax[2].set_ylabel('Sampled negative inertia');ax[2].set_xlabel('L — first sampled loss depends on resolution');ax[2].legend()
ax[0].set_title('Genuine screw-kernel geometry; same fixed target, no old node moved')
fig.savefig(P/'curve_geometry.png',dpi=160);plt.close(fig)
