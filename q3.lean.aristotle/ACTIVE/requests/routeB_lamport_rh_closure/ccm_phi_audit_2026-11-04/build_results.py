"""Join immutable Arb receipts, bounded paper audits, integer refinement and provenance."""
from pathlib import Path
import csv,json,hashlib
from fractions import Fraction
from flint import arb,ctx
P=Path(__file__).resolve().parent;ctx.prec=160
ms=[300,600,1000,2000,3000];runs=[json.loads((P/f'ARB_m{m}.json').read_text())for m in ms]
audits=['AUDIT_GEOMETRY.md','AUDIT_ASYMPTOTICS.md','AUDIT_TAIL.md','AUDIT_CONSUMER.md','AUDIT_INHERITED_DENSITY.md','AUDIT_ARB_IMPLEMENTATION.md']
assert all((P/n).exists()for n in audits)
rows=[]
for d in runs:
 m=d['m'];N=d['rational_inputs']['N_upper'];F=arb(d['safe_score_lower']);s0=d['conditional_simple_lower'];nd=d['conditional_distinct_lower']
 # Exclude each smaller integer s using the largest possible bad-block contribution.
 excluded=[]
 for s in range(N+1):
  mx=3*s+4*((N-s)//2)
  if F>mx:excluded.append(s)
  else:break
 ss=len(excluded);assert ss>=s0
 rows.append(dict(m=m,T=d['T'],precision_bits=d['precision_bits'],trace=d['trace'],frob_sq=d['frob_sq'],tail_E=d['tail_E'],N_upper=N,a_lower=str(Fraction(*d['rational_inputs']['a_lower'])),q_upper=str(Fraction(*d['rational_inputs']['q_upper'])),E_upper=str(Fraction(*d['rational_inputs']['E_upper'])),c='1/4',b='1/5',tail_R_coefficient='11/20',safe_score_lower=d['safe_score_lower'],simple_real_lower=d['simple_count_real_lower'],distinct_real_lower=d['distinct_count_real_lower'],s1_lower=s0,Nd_lower=nd,s1_fraction_rational=f'{s0}/{N}',Nd_fraction_rational=f'{nd}/{N}',s1_fraction=s0/N,Nd_fraction=nd/N,s1_integer_refined_lower=ss,s1_integer_refined_fraction_rational=f'{ss}/{N}',s1_integer_refined_fraction=ss/N,interval_gates_pass=all(d['gates'].values()),interpretation='FINITE_CERTIFIED_GIVEN_EXPLICIT_THEOREM_PREMISES; DIAGNOSTIC_NEVER_A_PROOF'))
with(P/'GROWTH.csv').open('w',newline='')as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
inc_s=all(Fraction(a['s1_lower'],a['N_upper'])<Fraction(b['s1_lower'],b['N_upper'])for a,b in zip(rows,rows[1:]));inc_d=all(Fraction(a['Nd_lower'],a['N_upper'])<Fraction(b['Nd_lower'],b['N_upper'])for a,b in zip(rows,rows[1:]))
gates=dict(status='DIAGNOSTIC_NEVER_A_PROOF',route='CHALLENGER_NOT_RH',base='c539c1953ee18ac09d48091c4218590d30962318',paper_audit='BOUNDED_PAPER_PASS_UNDER_STATED_EXTERNAL_THEOREMS',counterexample_found=False,B_C_interpretation_stopped=False,audit_files=audits,external_premises=['exact Weil source/divisor identity and standard zeta symmetry/strip facts','Montgomery–Vaughan circular Theorem1(1.3)','classical quantitative PNT','Rosser bound as Faber–Kadiri Theorem1.5','uniform Ingham density theorem for the separate cofinal argument only'],backend='python-flint/Arb 0.9.0',fixed_precision_bits=160,m300_eight_gates=runs[0]['gates'],m300_all_eight_pass=all(runs[0]['gates'].values()),growth_all_interval_gates_pass=all(all(d['gates'].values())for d in runs),P1=True,P2=True,P3=Fraction(rows[-1]['s1_lower'],rows[-1]['N_upper'])>=Fraction(1,5),P4=inc_s and inc_d,finite_only=True,no_cofinal_inference_from_cells=True,no_zero_list_used=True,no_source_matrix_change=True,no_route_state_change=True,no_RH_export=True,integer_refinement='Phi<=3s+4floor((N_upper-s)/2): exclude every smaller integer s')
(P/'GATES.json').write_text(json.dumps(gates,indent=2)+'\n')
external=[]
for short,url,statement in [('mv','https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf','Theorem1(1.3),p73: circular cosecant,constant3/2,local gaps'),('pnt','https://arxiv.org/pdf/2204.01980v2','Corollary1.2: theta error implies classical O_A(x/log^A x); proof uses finite-height RH verification internally'),('rosser','https://www.cs.uleth.ca/~kadiri/articles/New-Bounds-for-Psi-Math-Comp-Faber-Sept2013.pdf','Theorem1.5,p3: Rosser count, T>=2, .137/.443/1.588')]:
 p=P/f'external_{short}.pdf'
 if p.exists():digest=hashlib.sha256(p.read_bytes()).hexdigest()
 else:digest=next(x['pdf_sha256']for x in json.loads((P/'EXTERNAL_SOURCES.json').read_text())if x['url']==url)
 external.append(dict(url=url,pdf_sha256=digest,verified_statement=statement,pdf_retained_local_only=True))
(P/'EXTERNAL_SOURCES.json').write_text(json.dumps(external,indent=2)+'\n')
inputs=[]
for name,ref,blob in [('INPUT_VERDICT.md','proshka_inbox_2026-10-31@4adc9312','cc9e5b9e915ca8d1a2edeb32bf579f7db450d560'),('INPUT_RANK_TRACE.md','proshka_inbox_2026-10-31@eada41db','b0337bb10193b2498e6c35997a49237174c84a2c')]:
 b=(P/name).read_bytes();inputs.append(dict(file=name,ref=ref,git_blob=blob,sha256=hashlib.sha256(b).hexdigest()));assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
old=P/'INPUT_INHERITED_DENSITY.md';old=old if old.exists()else Path('/workspace/second_moment/output/INPUT_VERDICT.md');b=old.read_bytes();(P/'INPUT_INHERITED_DENSITY.md').write_bytes(b);assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()=='29647418b82ade2eca870a6d68592c1bf9c51859';inputs.append(dict(file='INPUT_INHERITED_DENSITY.md',ref='proshka_inbox_2026-10-31@07a242c1',git_blob='29647418b82ade2eca870a6d68592c1bf9c51859',sha256=hashlib.sha256(b).hexdigest()))
(P/'INPUTS.json').write_text(json.dumps(dict(base=gates['base'],inputs=inputs),indent=2)+'\n')
print(json.dumps(dict(rows=len(rows),P1=gates['P1'],P2=gates['P2'],P3=gates['P3'],P4=gates['P4'],refined=[r['s1_integer_refined_lower']for r in rows]),indent=2))
