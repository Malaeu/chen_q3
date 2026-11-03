from pathlib import Path
import json,csv,gzip,tarfile,io,hashlib
import numpy as np
P=Path(__file__).resolve().parent
from run import IN
base=list(csv.DictReader((IN/'SUMMARY.csv').open()));base={(r['world'],int(r['m'])):r for r in base}
records=[json.loads(f.read_text())for f in sorted((P/'cells').glob('*_768.json'))];rows=[]
for d in records:
 for r in d['summary']:
  b=r['best'];rows.append({k:r[k]for k in ['world','m','c','y','minimum','guard','resolved_negative_count','best_gap','max_gap_lower','max_gap_upper','status']}|{'q':b['q'],'r':b['r'],'delta':b['delta'],'lambda_r':b['lambda_r'],'sharp_gap':float(base[r['world'],r['m']]['best_gap']),'sharp_status':base[r['world'],r['m']]['separator_kappa_ge1'],'tail850_difference':r['tail_checks'][1]['operator_difference']})
assert len(rows)==108
assert {r['m']for r in rows if r['world']=='zeta'}==set(range(310,601,10))
with (P/'SUMMARY.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
controls=[]
for w in ['zeta','dh','plant']:
 a=json.loads((P/'cells'/f'{w}_600_768.json').read_text())['summary'];b=json.loads((P/'cells'/f'{w}_600_1024.json').read_text())['summary']
 for x,y in zip(a,b):
  diff=abs(x['best_gap']-y['best_gap']);assert diff<x['guard']
  controls.append(dict(world=w,c=x['c'],gap_difference=diff,same_best_q=x['best']['q']==y['best']['q'],guard=x['guard']))
(P/'FRAME_PRECISION_CHECK.json').write_text(json.dumps(controls,indent=2)+'\n')
stats={}
for c in [8.,16.,32.]:
 r=[x for x in rows if x['world']=='zeta'and x['c']==c];stats[c]={'passes':sum(x['status']=='PASS_NUMERIC'for x in r),'unresolved':sum(x['status']=='UNRESOLVED'for x in r),'gap_min':min(x['best_gap']for x in r),'gap_max':max(x['best_gap']for x in r)}
(P/'COUNTS.json').write_text(json.dumps(stats,indent=2)+'\n');print(json.dumps(stats,indent=2))
# One lossless archive: original input bytes and all complete sector receipts.
files=list((P/'cells').glob('*.json'))+[IN/n for n in ['zeta_zeros.csv','dh_zeros_900_200dps.json','SUMMARY.csv']];buf=io.BytesIO();members=[]
with tarfile.open(fileobj=buf,mode='w')as t:
 for f in sorted(files):
  name=('cells/'if f.parent.name=='cells'else'inputs/')+f.name;b=f.read_bytes();info=tarfile.TarInfo(name);info.size=len(b);info.mtime=0;t.addfile(info,io.BytesIO(b));members.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
data=gzip.compress(buf.getvalue(),mtime=0);(P/'data.tar.gz').write_bytes(data);parts=[]
for i,o in enumerate(range(0,len(data),250000)):
 name=f'data.tar.gz.part{i:02d}';b=data[o:o+250000];(P/name).write_bytes(b);parts.append(dict(path=name,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(P/'DATA_ARCHIVE.json').write_text(json.dumps(dict(archive_sha256=hashlib.sha256(data).hexdigest(),parts=parts,members=members),indent=2)+'\n')
# Standard scientific plot, unresolved levels omitted rather than shown as zero.
import os
os.environ['MPLCONFIGDIR']='/tmp/gaussian_mpl'
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
fig,ax=plt.subplots(1,2,figsize=(11,4))
for c in [8.,16.]:
 rr=sorted([x for x in rows if x['world']=='zeta'and x['c']==c],key=lambda x:x['m']);ax[0].semilogy([x['m']for x in rr],[x['best_gap']if x['status']=='PASS_NUMERIC'else np.nan for x in rr],'.-',label=f'c={c:g}')
ax[0].set(xlabel='m',ylabel='best separator gap',title='Zeta: c=32 unresolved throughout');ax[0].legend();ax[0].grid(alpha=.2)
sweep=list(csv.DictReader((P/'NEGATIVE_SWEEP.csv').open()))
for w in ['dh','plant']:
 rr=[x for x in sweep if x['world']==w and int(x['m'])==600];ax[1].plot([float(x['c'])for x in rr],[float(x['minimum'])for x in rr],'.-',label=w)
ax[1].set(xlabel='c, y=c/Omega(600)^2',ylabel='bottom eigenvalue',title='Retained negative levels at m=600');ax[1].legend();ax[1].grid(alpha=.2);fig.tight_layout();fig.savefig(P/'RESULT.png',dpi=150)
