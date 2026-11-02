"""Plot only positive-prefix innovation variances and first DH failure."""
from pathlib import Path
import os,csv
os.environ.setdefault('MPLCONFIGDIR','/tmp/screw_matplotlib')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
matplotlib.rcParams['svg.hashsalt']='SCREW_LINE_v1'
root=Path(__file__).resolve().parent
fig,axes=plt.subplots(1,2,figsize=(10,3.8),sharey=True)
for ax,mesh in zip(axes,[64,128]):
    for world,color in [('zeta','#237b9a'),('dh','#cb5348')]:
        rows=list(csv.DictReader((root/f'{world}_mesh{mesh}_dps160.csv').open()))
        if world=='dh':
            first=next(i for i,r in enumerate(rows) if r['positive']=='False')
            rows=rows[:first+1]
        x=[float(r['length']) for r in rows];y=[float(r['innovation']) for r in rows]
        ax.plot(x,y,label=world,color=color,linewidth=1.5)
        if world=='dh':ax.scatter(x[-1],y[-1],marker='x',s=45,color=color,zorder=3)
    ax.axhline(0,color='gray',lw=.7)
    ax.set_title(f'Fixed mesh Δ=1/{mesh}');ax.set_xlabel('Curve-segment length')
    ax.grid(alpha=.2);ax.set_yscale('symlog',linthresh=.001);ax.legend()
axes[0].set_ylabel('Innovation / signed Schur pivot')
fig.suptitle('Finite screw-increment geometry — diagnostic, never a proof',fontsize=11)
fig.tight_layout();fig.savefig(root/'innovation.svg',metadata={'Date':None});fig.savefig('/tmp/screw_geometry.png',dpi=130);plt.close(fig)
