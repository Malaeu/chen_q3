"""Apply fixed gates to both point replays; compare physical mathematical fields only."""
from pathlib import Path
import json,csv,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=90

def read(n):return json.loads((P/n).read_text())
def main():
 own=read('INDEPENDENT_RESULTS.json');other=read('APPENDIX_REPLAY.json');out=[];failures=[];comparisons=[];ratios=[]
 def gate(dps,backend,name,point,lhs,rhs,ok):
  out.append(dict(backend=backend,dps=dps,gate=name,point=point,lhs=mp.nstr(lhs,75),rhs=str(rhs),pass_gate=bool(ok)))
  if not ok:failures.append(dict(marker='DIAG_FORMULA_OR_NORMALIZATION_FAILURE',**out[-1]))
 for backend,data in [('independent',own['records']),('appendix',other['records'])]:
  for r in data:
   dps=r['dps'];tol=mp.mpf('1e-30')if dps==45 else mp.mpf('1e-50');plant=r['kind']=='PLANTED';label='7+i/3'if plant else r['gamma']
   real=mp.mpf(r['real_axis']['defect']if plant and backend=='independent'else r['real_axis_DH']['defect']if backend=='independent'else r['real_axis_defect']if plant else r['real_axis_DH_defect'])
   gate(dps,backend,'real_axis_unitarity',label,abs(real),tol,abs(real)<tol)
   if not plant:
    fe=mp.mpf(r['functional_equation_relative_error']);gate(dps,backend,'DH_functional_equation',label,fe,tol,fe<tol)
   errs=[]
   for s in r['samples']:
    eps=mp.mpf(s['epsilon']);point=label+'/'+s['epsilon'];node=s['plant'if plant else'DH']if backend=='independent'else s
    dd=mp.mpf(node['defect']if backend=='independent'or plant else node['DH_defect']);ratio=dd/(4*eps);err=mp.mpf(node['identity_error']if backend=='independent'else node['defect_identity_error']);errs.append(abs(ratio-1))
    gate(dps,backend,'defect_lower',point,dd,2*eps,dd>2*eps);gate(dps,backend,'defect_upper',point,dd,6*eps,dd<6*eps);gate(dps,backend,'identity_7_7',point,err,tol,err<tol)
    ratios.append(dict(backend=backend,dps=dps,kind=r['kind'],point=label,epsilon=s['epsilon'],ratio_to_4eps=mp.nstr(ratio,75),abs_ratio_deviation=mp.nstr(abs(ratio-1),75)))
    if not plant or backend=='independent':
     for name in ['zeta','curve']:
      defect=mp.mpf(s[name+'_control']['defect']if backend=='independent'else s[name+'_control_defect']);gate(dps,backend,name+'_nonpositive_control',point,defect,tol,defect<=tol)
      if backend=='independent':
       er=mp.mpf(s[name+'_control']['identity_error']);gate(dps,backend,name+'_identity_7_7',point,er,tol,er<tol)
   gate(dps,backend,'ratio_toward_one',label,errs[1],errs[0],errs[1]<errs[0])
 # Common physical fields, rather than time-dependent JSON hashes.
 for a in own['records']:
  plant=a['kind']=='PLANTED';candidates=[b for b in other['records']if b['dps']==a['dps']and b['kind']==a['kind']and(plant or abs(mp.mpf(b['gamma'])-mp.mpf(a['gamma']))<mp.mpf('1e-20'))];assert len(candidates)==1;b=candidates[0]
  fields=[]
  if not plant:fields +=[(k,a[k],b[k])for k in ['beta','gamma']]
  for x,y in zip(a['samples'],b['samples']):
   assert x['epsilon']==y['epsilon'];node=x['plant'if plant else'DH'];fields +=[(x['epsilon']+'/'+k,node[k],y['defect'if plant else'DH_defect']if k=='defect'else y[k])for k in ['defect','ratio_to_4eps']]
   if not plant:fields +=[(x['epsilon']+'/'+name,x[name+'_control']['defect'],y[name+'_control_defect'])for name in ['zeta','curve']]
  for name,x,y in fields:
   xx,yy=mp.mpf(x),mp.mpf(y);delta=abs(xx-yy);scaled=delta/max(1,abs(xx),abs(yy));ok=scaled<mp.mpf('1e-29')
   comparisons.append(dict(dps=a['dps'],kind=a['kind'],point='7+i/3'if plant else a['address_label'],field=name,independent=x,appendix=y,abs_difference=mp.nstr(delta,75),scaled_difference=mp.nstr(scaled,75),pass_gate=bool(ok)))
   if not ok:failures.append(dict(marker='DIAG_FORMULA_OR_NORMALIZATION_FAILURE',gate='replay_math_field_comparison',dps=a['dps'],point=str(a.get('address_label'))+'/'+name,lhs=x,rhs=y))
 summary=[]
 for backend in ['independent','appendix']:
  for dps in [45,70]:
   for eps in ['0.001','0.0001']:
    rr=[x for x in ratios if x['backend']==backend and x['dps']==dps and x['epsilon']==eps];worst=max(rr,key=lambda r:mp.mpf(r['abs_ratio_deviation']));summary.append(dict(backend=backend,dps=dps,epsilon=eps,max_abs_ratio_deviation=worst['abs_ratio_deviation'],at_kind=worst['kind'],at_point=worst['point'],max_deviation_less_0_001=mp.mpf(worst['abs_ratio_deviation'])<mp.mpf('.001')))
 result=dict(status='PASS_DIAG_NOT_INTERVAL'if not failures else'DIAG_FORMULA_OR_NORMALIZATION_FAILURE',gate_records=out,gate_count=len(out),failure_count=len(failures),failures=failures,max_ratio_deviations=summary,mathematical_field_comparison_count=len(comparisons),all_mathematical_comparisons_pass=all(x['pass_gate']for x in comparisons),max_scaled_math_field_difference=mp.nstr(max(mp.mpf(r['scaled_difference'])for r in comparisons),75),comparison_tolerance='1e-29 scaled to max(1,abs(x),abs(y)); Appendix output has32 significant digits',math_fields_excluded_from_exact_matching=['elapsed_seconds','root_residual','rounding/identity diagnostics; gated individually'],appendix_scope_note='Appendix lacks zeta/curve controls at plant points; independent implementation adds and gates both there. Appendix source is unmodified.')
 (P/'GATES.json').write_text(json.dumps(result,indent=2)+'\n')
 for name,rs in [('GATE_TABLE.csv',out),('REPLAY_COMPARISON.csv',comparisons),('RATIO_DEVIATIONS.csv',summary)]:
  with(P/name).open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=list(rs[0]));w.writeheader();w.writerows(rs)
 print(json.dumps(dict(status=result['status'],gates=len(out),math_fields=len(comparisons),max_scaled_math_difference=result['max_scaled_math_field_difference'],ratios=summary,failures=failures),indent=2))
 if failures:raise SystemExit(1)
if __name__=='__main__':main()
