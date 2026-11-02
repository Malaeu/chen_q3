import json,sys,csv,hashlib
from pathlib import Path
import mpmath as mp
mp.mp.dps=160
OUT=Path(__file__).resolve().parent
rows=json.loads((OUT/'spectra_dps140_gl160.json').read_text())
Z=OUT.parents[1]/'lowcluster_2026-11-02/ladder_limit/identify/zero_height_local/zeros.csv'
zeros=[mp.mpf(r['gamma']) for r in csv.DictReader(Z.open())]
comparisons=[]
for r in rows:
 m=r['m'];r['zero_counts']={}
 for label,T in [('2pi_m_over_log_m',2*mp.pi*m/mp.log(m)),('2pi_m',2*mp.pi*m)]:
  count=sum(g<T for g in zeros)
  r['zero_counts'][label]=dict(T=mp.nstr(T,140),count=count,previous_gamma=mp.nstr(zeros[count-1],140),next_gamma=mp.nstr(zeros[count],140),lower_margin=mp.nstr(T-zeros[count-1],140),upper_margin=mp.nstr(zeros[count]-T,140))
 p=OUT.parent/f'spectra_m{m}_dps100_gl128.json'
 if not p.exists():continue
 a=json.loads(p.read_text());ev=list(map(mp.mpf,r['eigenvalues']));v=list(map(mp.mpf,a['lambda']))
 for B in [2,4,8]:
  eps=mp.mpf(m)**(-B);margin=min(abs(abs(x)-eps) for x in ev);err=max(abs(x-y) for x,y in zip(ev,v))
  comparisons.append(dict(m=m,B=B,main_count=sum(abs(x)<eps for x in v),validation_count=sum(abs(x)<eps for x in ev),validation_margin=mp.nstr(margin,120),max_absolute_eigenvalue_difference=mp.nstr(err,120),error_over_margin=mp.nstr(err/margin,120),zero_count_log=r['zero_counts']['2pi_m_over_log_m']['count'],zero_count_plain=r['zero_counts']['2pi_m']['count'],main_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(OUT/'spectra_dps140_gl160.json').write_text(json.dumps(rows,indent=2)+'\n')
(OUT/'comparison.json').write_text(json.dumps(comparisons,indent=2)+'\n')
print(json.dumps(comparisons,indent=2))
