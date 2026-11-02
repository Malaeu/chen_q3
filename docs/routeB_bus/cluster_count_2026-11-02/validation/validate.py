"""Independent high precision count validation; diagnostic, not interval certified."""
import sys,json,csv,hashlib,time
from pathlib import Path
import mpmath as mp
OUT=Path(__file__).resolve().parent
BUS=OUT.parents[1]
sys.path.insert(0,str(BUS/'phase_space_V'))
from v_forms import build_forms
mp.mp.dps=140
ZPATH=BUS/'lowcluster_2026-11-02/ladder_limit/identify/zero_height_local/zeros.csv'
zeros=[mp.mpf(r['gamma']) for r in csv.DictReader(ZPATH.open())]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
results=[]
for m in [8,24,40]:
 start=time.monotonic();forms=build_forms(m,m,140,160);ev=mp.eigsy(forms['K'],eigvals_only=True)
 row=dict(m=m,dps=140,order=160,eigenvalues=[mp.nstr(x,140) for x in ev],counts={})
 for B in [2,4,8]:
  eps=mp.mpf(m)**(-B);d=[abs(abs(x)-eps) for x in ev];j=min(range(len(d)),key=lambda j:d[j])
  row['counts'][str(B)]=dict(epsilon=mp.nstr(eps,140),count=sum(abs(x)<eps for x in ev),nearest_index=j,nearest_eigenvalue=mp.nstr(ev[j],140),absolute_threshold_margin=mp.nstr(d[j],140),relative_threshold_margin=mp.nstr(d[j]/eps,140))
 T=2*mp.pi*m/mp.log(m);cnt=sum(g<=T for g in zeros)
 row['zero_count_max_physical_frequency']=dict(T=mp.nstr(T,140),N_T=cnt,previous_gamma=mp.nstr(zeros[cnt-1],140) if cnt else None,next_gamma=mp.nstr(zeros[cnt],140))
 row['source_hashes']={str(p.relative_to(BUS)):sha(p) for p in [BUS/'phase_space_V/v_forms.py',ZPATH,Path(__file__)]}
 row['seconds']=time.monotonic()-start;results.append(row)
 (OUT/'spectra_dps140_gl160.json').write_text(json.dumps(results,indent=2)+'\n')
 print(m,'counts',[row['counts'][str(B)]['count'] for B in [2,4,8]],'N(T)',cnt,'seconds',row['seconds'],flush=True)
# Both requested strict-count cutoffs. The literal modal cutoff equals the first.
for row in results:
 m=row['m'];row['zero_counts']={}
 for label,T in [('2pi_m_over_log_m',2*mp.pi*m/mp.log(m)),('2pi_m',2*mp.pi*m)]:
  cnt=sum(g<T for g in zeros)
  row['zero_counts'][label]=dict(T=mp.nstr(T,140),count=cnt,previous_gamma=mp.nstr(zeros[cnt-1],140),next_gamma=mp.nstr(zeros[cnt],140),lower_margin=mp.nstr(T-zeros[cnt-1],140),upper_margin=mp.nstr(zeros[cnt]-T,140))
 row['source_hashes'][str(Path(__file__).relative_to(BUS))]=sha(Path(__file__))
(OUT/'spectra_dps140_gl160.json').write_text(json.dumps(results,indent=2)+'\n')
