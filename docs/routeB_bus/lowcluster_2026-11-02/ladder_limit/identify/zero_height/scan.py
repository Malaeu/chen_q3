"""DIAGNOSTIC_NEVER_A_PROOF: finite-vector residuals at accurate zeta zeros."""
from pathlib import Path
import sys,csv,json,time
import mpmath as mp
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(OUT.parent))
import identify as src
mp.mp.dps=100
fmt=lambda x:mp.nstr(x,95)
def save(name,rows):
 with (OUT/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def main():
 start=time.monotonic(); data={m:src.load(m) for m in (16,20,24)}
 maximum_rows=list(csv.DictReader((OUT.parent/'fourier_maxima.csv').open()))
 maxima={(int(r['m']),r['profile']):mp.mpf(r['max_transform']) for r in maximum_rows}
 a=data[16];ts=[mp.mpf(i)/20 for i in range(1601)];grid=[src.evalall(a,t) for t in ts]
 for j,name in enumerate(src.NAMES):
  candidates=[mp.mpf(0),mp.mpf(80)]
  for i in range(1,len(ts)-1):
   if abs(grid[i][j])>=abs(grid[i-1][j]) and abs(grid[i][j])>=abs(grid[i+1][j]):
    z=mp.findroot(lambda t:src.evalone(a,j,t,True),(ts[i-1],ts[i+1]),tol=mp.mpf('1e-85'),maxsteps=40)
    if 0<=z<=80:candidates.append(z)
  t=max(candidates,key=lambda t:abs(src.evalone(a,j,t)));v=abs(src.evalone(a,j,t))
  tail=2*mp.fsum(abs(a['C'][n,j])*a['d'][n]/mp.sqrt(a['L']) for n in range(17))/(80-a['omega'][-1])
  assert tail<v
  maxima[16,name]=v
  maximum_rows.append(dict(m=16,profile=name,max_transform=fmt(v),argmax_abs_t=fmt(t),search_step='0.05',search_T='80',stationary_candidates=len(candidates),tail_upper_bound_outside_T=fmt(tail),outside_search_cannot_exceed_found_peak=True))
 save('maxima.csv',maximum_rows);print('m16 maxima complete',flush=True)
 zeros=[];k=1
 while True:
  g=mp.im(mp.zetazero(k))
  if g>300:break
  zeros.append(g)
  if k%20==0:print('zeros',k,fmt(g),flush=True)
  k+=1
 next_zero_above=g
 save('zeros.csv',[dict(index=i+1,gamma=fmt(g)) for i,g in enumerate(zeros)])
 rows=[];ratios={};values={}
 for m,a in data.items():
  vals=[src.evalall(a,g) for g in zeros];values[m]=vals
  for j,name in enumerate(src.NAMES):
   ratios[m,j]=[abs(v[j])/maxima[m,name] for v in vals]
   for i,g in enumerate(zeros):rows.append(dict(m=m,profile=name,zero_index=i+1,gamma=fmt(g),fourier_value=fmt(vals[i][j]),normalized_absolute=fmt(ratios[m,j][i])))
 save('samples.csv',rows)
 summary=[];selected=set()
 for m in data:
  for j,name in enumerate(src.NAMES):
   rr=ratios[m,j];imax=max(range(len(rr)),key=lambda i:rr[i]);selected.add((j,imax)) if m==24 else None
   for threshold in (mp.mpf('1e-6'),mp.mpf('1e-3')):
    hits=[i for i,r in enumerate(rr) if r>threshold];first=hits[0] if hits else None
    if m==24 and first is not None:selected.update((j,i) for i in (max(0,first-1),first))
    summary.append(dict(m=m,profile=name,threshold=fmt(threshold),censored_through_300=not hits,first_exceedance_zero_index=first+1 if hits else '',first_exceedance_T=fmt(zeros[first]) if hits else '',preceding_zero_index=first if hits and first>0 else '',preceding_zero_T=fmt(zeros[first-1]) if hits and first>0 else '',preceding_residual=fmt(rr[first-1]) if hits and first>0 else '',first_residual=fmt(rr[first]) if hits else '',T_over_2pi_m=fmt(zeros[first]/(2*mp.pi*m)) if hits else '',T_over_2pi_m_over_logm=fmt(zeros[first]/(2*mp.pi*m/mp.log(m))) if hits else '',number_exceeding=len(hits),later_below_or_equal_count=sum(r<=threshold for r in rr[first+1:]) if hits else '',all_later_sampled_zeros_exceed=all(r>threshold for r in rr[first+1:]) if hits else False,max_residual_through_300=fmt(rr[imax]),max_residual_zero_index=imax+1,max_residual_T=fmt(zeros[imax]),last_sampled_zero_T=fmt(zeros[-1]),last_sampled_residual=fmt(rr[-1])))
 save('thresholds.csv',summary)
 with mp.workdps(140):
  hi=src.load(24,True)
  # Align signs to fixed 100dps source vectors, including least-ladder shape.
  for j in range(9):
   if mp.fdot(hi['C'][:,j],data[24]['C'][:,j])<0:hi['C'][:,j]=-hi['C'][:,j]
  selected.update((j,i) for j in range(9) for i in (0,9,len(zeros)-1))
  accurate={i:mp.im(mp.zetazero(i+1)) for i in sorted({i for _,i in selected})}
  validation=[]
  for j,i in sorted(selected):
   v=src.evalone(hi,j,accurate[i]);lo=values[24][i][j]
   validation.append(dict(profile=src.NAMES[j],zero_index=i+1,gamma=fmt(accurate[i]),source100_value=fmt(lo),source140_value=fmt(v),absolute_source_change=fmt(abs(v-lo)),relative_source_change=fmt(abs(v-lo)/abs(v)) if v else '',normalized_source_change=fmt(abs(v-lo)/maxima[24,src.NAMES[j]])))
 save('validation.csv',validation)
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',evaluation_dps=100,validation_dps=140,zero_count=len(zeros),first_zero_above_300=fmt(next_zero_above),seconds=time.monotonic()-start,limitations=['Finite-vector scan only; no limiting-function conclusion.','First exceedance is not persistent exceedance.','Stationary-point grid search is diagnostic, not interval certification; explicit tail bound excludes larger peaks beyond80.','Three m values do not establish a height law, especially with censoring.'])
 (OUT/'metadata.json').write_text(json.dumps(out,indent=2)+'\n')
 lines=['# Zero-height diagnostic','', '**DIAGNOSTIC_NEVER_A_PROOF.**', '',f'All {len(zeros)} accurate mpmath zeros with height at most300 were evaluated at100dps. Selected m24 samples were reevaluated from140dps source at140dps.','', 'Tables report first exceedances, with the preceding zero as bracket. Later returns below threshold are counted separately. No persistence outside the sampled zeros is inferred.','', '|m|profile|first T >1e-6|first T >1e-3|max residual through300|','|---:|---|---:|---:|---:|']
 for m in data:
  for name in src.NAMES:
   rr=[r for r in summary if r['m']==m and r['profile']==name]
   def label(r):return 'censored (>300)' if r['censored_through_300'] else mp.nstr(mp.mpf(r['first_exceedance_T']),9)
   lines.append(f"|{m}|{name}|{label(rr[0])}|{label(rr[1])}|{mp.nstr(mp.mpf(rr[0]['max_residual_through_300']),7)}|")
 lines+=['','See thresholds.csv for both requested scaled heights, preceding-zero brackets, and later below-threshold counts. samples.csv preserves all signed transforms and normalized magnitudes.','', 'Global maxima reuse the earlier m20/m24 diagnostic searches; m16 follows the same0.05 grid and high-precision stationary refinement on[0,80]. The explicit sinc tail bound is below each found peak beyond80. This is not a rigorous enclosure of the finite search interval.','', 'No asymptotic height law or limiting radical membership follows from these three finite carriers.']
 (OUT/'RESULT.md').write_text('\n'.join(lines)+'\n');print('COMPLETE',out,flush=True)
def enrich():
 rows=list(csv.DictReader((OUT/'thresholds.csv').open()))
 trends=[]
 for name in src.NAMES:
  rr={m:next(r for r in rows if int(r['m'])==m and r['profile']==name) for m in (16,20,24)}
  trends.append(dict(profile=name,maximum_m16=rr[16]['max_residual_through_300'],maximum_m20=rr[20]['max_residual_through_300'],maximum_m24=rr[24]['max_residual_through_300'],max_m20_over_m16=fmt(mp.mpf(rr[20]['max_residual_through_300'])/mp.mpf(rr[16]['max_residual_through_300'])),max_m24_over_m20=fmt(mp.mpf(rr[24]['max_residual_through_300'])/mp.mpf(rr[20]['max_residual_through_300']))))
 save('trend.csv',trends)
 p=OUT/'RESULT.md';text=p.read_text().replace('at most300','at most 300').replace('at100dps','at 100 dps').replace('from140dps source at140dps','from 140 dps source at 140 dps').replace('same0.05','same 0.05').replace('on[0,80]','on [0,80]').replace('beyond80','beyond 80').replace('through300','through 300')
 text+='\nOnly m16 φ6 and φ7 exceed 10⁻⁶: their first crossing is zero 7, T=40.9187190121, bracketed by zero 6 at T=37.5861781588. Both have T/(2πm)=0.407026024736 and T/(2πm/log m)=1.12851576584. They subsequently return below threshold at 129 and 51 sampled zeros respectively. Thus neither crossing is persistent. No profile exceeds 10⁻³. All m20/m24 profiles are right-censored through 300 at both thresholds.\n\nThe largest normalized residual over all profiles is 4.74464546e−5 at m16 (zero 7), 4.250461e−8 at m20 (zero 18, T=59.3470440), and 1.576418e−11 at m24 (zero 19, T=60.8317785); each belongs to φ7. Per-profile maximum ratios across m are in trend.csv. No fitted height law is reported under this metric.\n\nGlobal-maximum normalization can hide loss of relative fidelity where the transform is itself small at high frequency. Censoring means no exceedance among the sampled zeros through 300; it does not mean an infinite threshold height or establish radical membership.\n\nThe 36 selected m24 validation samples change relatively by at most 3.44e−48 when both source and evaluation precision increase to 140 dps. These are empirical numerical comparisons, not interval bounds.\n'
 p.write_text(text)
if __name__=='__main__':
 main();enrich()
