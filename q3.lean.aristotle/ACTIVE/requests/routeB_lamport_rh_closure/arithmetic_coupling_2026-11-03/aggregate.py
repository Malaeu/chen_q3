"""Aggregate ε-relaxed affine PSD diagnostics; do not promote tiny quiet signs."""
from pathlib import Path
import json,csv,collections,numpy as np
P=Path(__file__).resolve().parent
def write(name,rows):
 keys=list(dict.fromkeys(k for r in rows for k in r))
 with(P/name).open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
primary=[];ends=[];empties=[];sens=[]
for path in sorted((P/'cells').glob('*.json')):
 j=json.loads(path.read_text());r=dict(j['summary']);factor=r['epsilon_factor'];m=r['m'];world=r['world']
 if r['status']=='NONEMPTY_NUMERIC':
  r['width']=r['u_upper_minus_one']-r['u_lower_minus_one'];r['lower_offset_over_epsilon']=r['u_lower_minus_one']/r['epsilon'];r['upper_offset_over_epsilon']=r['u_upper_minus_one']/r['epsilon']
 if factor!=100:sens.append(r);continue
 primary.append(r)
 if r['status']=='NONEMPTY_NUMERIC':
  for e in j['solver']['endpoints']:ends.append(dict(world=world,m=m,epsilon=r['epsilon'],**{k:v for k,v in e.items()if k!='carrier_vector'}))
 elif r['status']=='EMPTY_NUMERIC':
  Q=np.load(P/'quiet/frames'/f'{"dh"if world=="dh"else"zeta"}_m{m}.npz')['Q'];s=j['solver'];empties.append(dict(world=world,m=m,epsilon=r['epsilon'],necessary_u_lower=s['outer_lower'],necessary_u_upper=s['outer_upper'],dual_constant=s['dual_constant'],dual_slope_residual=s['dual_slope'],dual_guard=s['dual_guard'],dual_margin_in_guards=-s['dual_constant']/s['dual_guard'],lower_cut_quiet_mass=float(np.linalg.norm(Q.T@np.array(s['lower_vector']))**2),upper_cut_quiet_mass=float(np.linalg.norm(Q.T@np.array(s['upper_vector']))**2),baseline_negative_witness_quiet_mass=r['baseline_negative_witness_quiet_mass'],history_trials=len(s['history'])))
primary.sort(key=lambda r:(r['world'],r['m']));write('SUMMARY.csv',primary);write('ENDPOINTS.csv',ends);write('EMPTY_WITNESSES.csv',empties);write('EPSILON_SENSITIVITY.csv',sens)
summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',primary_cells=len(primary),sensitivity_cells=len(sens),epsilon_rule='epsilon=100 rho_m; rho_m=1000 eps64 (m+1) max_world(||C||2+||B||2,1)',statuses={w:dict(collections.Counter(r['status']for r in primary if r['world']==w))for w in ['zeta','double2','dh']},epsilon_range=[min(r['epsilon']for r in primary),max(r['epsilon']for r in primary)],zeta_quiet_minima_unresolved=sum(r['quiet_lambda_min_status']=='UNRESOLVED_AT_FLOAT_FLOOR'for r in primary if r['world']=='zeta'),all_endpoints_quiet_mass_min=min(e['quiet_mass']for e in ends),max_endpoint_shifted_residual=max(e['endpoint_shifted_residual']for e in ends),min_empty_dual_margin_in_guards=min(r['dual_margin_in_guards']for r in empties),smallest_quiet_relation='All285binary64ζminima unresolved; relationship only numerically resolved in independent MP16/24/40 pilots',exact_I0_claim=False)
(P/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
fig,ax=plt.subplots(1,3,figsize=(13,3.8),layout='constrained');z=[r for r in primary if r['world']=='zeta'];m=[r['m']for r in z]
ax[0].semilogy(m,[-r['u_lower_minus_one']for r in z],color='#168b89',label='1-u_minus');ax[0].semilogy(m,[r['u_upper_minus_one']for r in z],color='#df755d',label='u_plus-1');ax[0].set(xlabel='m',ylabel='absolute endpoint offset; binary64 epsilon tube');ax[0].legend()
ax[1].plot(m,[-r['lower_offset_over_epsilon']for r in z],color='#168b89',label='(1-u_minus)/epsilon');ax[1].plot(m,[r['upper_offset_over_epsilon']for r in z],color='#df755d',label='(u_plus-1)/epsilon');ax[1].set(xlabel='m',ylabel='offset / chosen epsilon');ax[1].legend(fontsize=8)
mp=list(csv.DictReader((P/'mp_pilots/EPSILON_SENSITIVITY.csv').open()))
for mm in [16,24,40]:
 a=[r for r in mp if int(r['m'])==mm];ax[2].loglog([float(r['epsilon'])for r in a],[float(r['width'])for r in a],'o-',label='m='+str(mm))
ax[2].set(xlabel='epsilon (MP pilots)',ylabel='coupling interval width');ax[2].legend();fig.suptitle('Literal even CCM: tolerance widths versus resolved small-window scales');fig.savefig(P/'COUPLING.png',dpi=170);fig.savefig(P/'COUPLING.svg');plt.close(fig)
q={int(r['m']):float(r['minimum_quiet_lambda'])for r in csv.DictReader((P/'mp_pilots/QUIET.csv').open())};fig,ax=plt.subplots(figsize=(5.5,4),layout='constrained')
for side,col,label in [('u_minus_minus_1','#168b89','1-u_minus'),('u_plus_minus_1','#df755d','u_plus-1')]:
 a=[r for r in mp if float(r['epsilon'])==1e-100];ax.loglog([q[int(r['m'])]for r in a],[abs(float(r[side]))for r in a],'o-',color=col,label=label)
 for r in a:ax.annotate('m'+r['m'],(q[int(r['m'])],abs(float(r[side]))),xytext=(4,3),textcoords='offset points',fontsize=8)
xx=np.array([min(q.values()),max(q.values())]);ax.loglog(xx,10*xx,':',color='#777',label='10 x quiet minimum (reference)');ax.set(xlabel='smallest quiet eigenvalue (MP, three windows only)',ylabel='endpoint offset at epsilon=1e-100');ax.legend(fontsize=8);fig.savefig(P/'QUIET_RELATION.png',dpi=170);fig.savefig(P/'QUIET_RELATION.svg');plt.close(fig)
