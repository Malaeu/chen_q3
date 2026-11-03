import os
os.environ['MPLCONFIGDIR']='/tmp/stiffness_mpl';os.environ['XDG_CACHE_HOME']='/tmp/stiffness_cache'
from pathlib import Path
import json,csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent;fig,ax=plt.subplots(1,3,figsize=(14,4))
ms=[16,24,40];colors=['#277f84','#e58972','#6b7280']
for k,m in enumerate(ms):
 d=json.loads((P/f'mp_prices_m{m}.json').read_text());rows=d['literal_face']['P3_optimizer_labeled'];v={r['knob']:float(r['price'])for r in rows};vals=[v['C_Gamma'],v['C_pole'],v['B_2'],sum(x for key,x in v.items()if key not in ['C_Gamma','C_pole','B_2'])];ax[0].bar(np.arange(4)+(k-1)*.24,vals,width=.24,label=f'm={m}',color=colors[k])
ax[0].set_xticks(range(4),['Gamma','pole','p=2','other primes']);ax[0].axhline(0,color='black',linewidth=.6);ax[0].set_title('MP rank-one face: signed prices');ax[0].legend()
b=[json.loads((P/'binary_cells'/f'zeta_m{m}.json').read_text())['face_size']for m in ms];ax[1].plot(ms,b,'o-',label='binary source floor');ax[1].plot(ms,[1,1,1],'s-',label='MP source floor');ax[1].set(xlabel='m',ylabel='selected cluster size',title='The selected face depends on precision');ax[1].legend()
r=[x for x in csv.DictReader((P/'p5_summary.csv').open())if x['precision']!='binary64_calibration'];r.sort(key=lambda x:int(x['m']))
for key,label,marker in [('full_crossing','full crossing','o'),('registered_prediction','registered prediction','s'),('corrected_threshold_prediction','corrected prediction','x')]:ax[2].semilogy([int(x['m'])for x in r],[float(x[key])for x in r],marker+'-',label=label)
ax[2].set(xlabel='m',ylabel='a',title='MP finite-threshold a-dial');ax[2].legend(fontsize=8)
for a in ax:a.grid(alpha=.15)
fig.tight_layout();fig.savefig(P/'RESULT.png',dpi=150)
