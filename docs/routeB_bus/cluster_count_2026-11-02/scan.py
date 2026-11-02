"""DIAGNOSTIC_NEVER_A_PROOF: literal even-carrier small-eigenvalue counts."""
from pathlib import Path
import sys,csv,json,time,hashlib
import mpmath as mp
OUT=Path(__file__).resolve().parent
BASE=OUT.parent
sys.path.insert(0,str(BASE/'phase_space_V'))
from v_forms import build_forms
ZERO=BASE/'lowcluster_2026-11-02/ladder_limit/identify/zero_height_local/zeros.csv'

def cell(m,dps=100,order=128):
 start=time.monotonic();forms=build_forms(m,m,dps,order);ev=mp.eigsy(forms['K'],eigvals_only=True)
 r={'status':'DIAGNOSTIC_NEVER_A_PROOF','m':m,'N':m,'dimension':m+1,'dps':dps,'order':order,'lambda':[mp.nstr(x,dps) for x in ev],'L':mp.nstr(forms['L'],dps),'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256((BASE/'phase_space_V/v_forms.py').read_bytes()).hexdigest()}
 (OUT/f'spectra_m{m}_dps{dps}_gl{order}.json').write_text(json.dumps(r,indent=2)+'\n');print('done',m,r['seconds'],flush=True)

def save(name,rows):
 with (OUT/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def summarize():
 mp.mp.dps=120;zeros=[mp.mpf(r['gamma']) for r in csv.DictReader(ZERO.open())];counts=[];spectra=[];f=lambda x:mp.nstr(x,90)
 for m in range(8,41):
  r=json.loads((OUT/f'spectra_m{m}_dps100_gl128.json').read_text());ev=list(map(mp.mpf,r['lambda']));dim=m+1
  Tlog=2*mp.pi*m/mp.log(m);Tplain=2*mp.pi*m
  nlog=sum(t<Tlog for t in zeros);nplain=sum(t<Tplain for t in zeros)
  for i,x in enumerate(ev):spectra.append(dict(m=m,index=i,lambda_=f(x),sign=int(mp.sign(x)),dps=r['dps'],order=r['order']))
  for B in (2,4,8):
   mu=mp.mpf(m)**(-B);absolute=sum(abs(x)<mu for x in ev);signed=sum(x<mu for x in ev);negoutside=sum(x<=-mu for x in ev)
   counts.append(dict(m=m,N=m,dimension=dim,B=B,mu=f(mu),count_abs_lambda_lt_mu=absolute,count_signed_lambda_lt_mu=signed,negative_outside_abs_band=negoutside,total_negative=sum(x<0 for x in ev),minimum_lambda=f(ev[0]),threshold_absolute_margin=f(min(abs(abs(x)-mu) for x in ev)),threshold_relative_margin=f(min(abs(abs(x)-mu) for x in ev)/mu),signed_threshold_margin=f(min(abs(x-mu) for x in ev)),T_2pi_m_over_logm=f(Tlog),T_2pi_N_over_L=f(Tlog),Nzeros_Tlog=nlog,prediction_dimension_minus_Nzeros_Tlog=dim-nlog,T_2pi_m=f(Tplain),Nzeros_Tplain=nplain,prediction_dimension_minus_Nzeros_Tplain=dim-nplain,abs_count_minus_log_prediction=absolute-(dim-nlog),abs_count_minus_plain_prediction=absolute-(dim-nplain),signed_count_minus_log_prediction=signed-(dim-nlog),signed_count_minus_plain_prediction=signed-(dim-nplain),nearest_zero_distance_Tlog=f(min(abs(t-Tlog) for t in zeros)),nearest_zero_distance_Tplain=f(min(abs(t-Tplain) for t in zeros))))
 save('spectra.csv',spectra);save('counts.csv',counts)
 meta={'status':'DIAGNOSTIC_NEVER_A_PROOF','dps':100,'order':128,'m_range':[8,40],'B':[2,4,8],'zero_count_available':len(zeros),'zero_source_sha256':hashlib.sha256(ZERO.read_bytes()).hexdigest(),'zero_cutoff_covered':max(zeros)>2*mp.pi*40,'definitions':{'absolute':'abs(lambda)<mu','signed':'lambda<mu','negative_outside':'lambda<=-mu','Nzeros':'number of stored positive ordinates < cutoff'},'minimum_relative_threshold_margin':f(min(mp.mpf(r['threshold_relative_margin']) for r in counts)),'negative_cells':[r['m'] for r in counts if r['B']==2 and r['total_negative']>0]}
 (OUT/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
 lines=['# Literal even cluster counts','','**DIAGNOSTIC_NEVER_A_PROOF.**','','Every integer m=8…40 uses N=m, L=log m, 100 dps and GL128. All prime powers are preserved. Absolute and signed counts and their threshold margins are in counts.csv. N(T) counts positive zeta ordinates only; both cutoffs lie below the stored zero-table limit.','','|m|count B2|count B4|count B8|d−N(2πm/log m)|d−N(2πm)|','|---:|---:|---:|---:|---:|---:|']
 for m in range(8,41):
  rs=[r for r in counts if r['m']==m];lines.append('|'+ '|'.join(map(str,[m,*[r['count_abs_lambda_lt_mu'] for r in rs],rs[0]['prediction_dimension_minus_Nzeros_Tlog'],rs[0]['prediction_dimension_minus_Nzeros_Tplain']]))+'|')
 lines+=['',f"Minimum relative distance from any absolute-band threshold: {mp.nstr(mp.mpf(meta['minimum_relative_threshold_margin']),12)}.",'','The literal cutoff 2πN/L equals 2πm/log m here. Negative values of d−N(2πm) are reported without clipping. No cofinal counting law or sign theorem is inferred.']
 (OUT/'RESULT.md').write_text('\n'.join(lines)+'\n');print('summary complete',flush=True)
if __name__=='__main__':
 if sys.argv[1]=='summarize':summarize()
 else:
  for m in map(int,sys.argv[1:]):cell(m)
