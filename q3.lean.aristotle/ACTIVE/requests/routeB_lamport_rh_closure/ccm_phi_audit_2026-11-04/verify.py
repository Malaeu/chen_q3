"""Verify interval certificates, finite integer transfer and packet integrity offline."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,csv,math
from flint import arb,ctx
P=Path(__file__).resolve().parent;ctx.prec=160
ms=[300,600,1000,2000,3000];growth=list(csv.DictReader((P/'GROWTH.csv').open()));assert len(growth)==5
for m,r in zip(ms,growth):
 d=json.loads((P/f'ARB_m{m}.json').read_text());assert int(r['m'])==m==d['m'] and d['precision_bits']==160
 assert not d['uses_zero_list']and not d['uses_source_array']and all(d['gates'].values())
 L=arb(m).log();sig=L+arb(1)/5;inp=d['rational_inputs'];a=arb(inp['a_lower'][0])/inp['a_lower'][1];q=arb(inp['q_upper'][0])/inp['q_upper'][1];E=arb(inp['E_upper'][0])/inp['E_upper'][1];N=inp['N_upper']
 assert arb(d['trace'])>a and arb(d['frob_sq'])<q and arb(d['tail_E'])<E and arb(d['N_upper_real'])<N+1
 kap=1+(1+L.log())/(4*L);T=kap*2*arb.pi()*m/L;assert T.overlaps(arb(d['T']))
 assert arb(d['Rosser_R_over_log'])<arb(11)/20 and T.log()>1
 assert arb(d['zero_free_gamma5_error'])<arb(1)/2
 F=4*a/sig-4*E/sig-(q.sqrt()/sig+E/sig)**2;assert F.overlaps(arb(d['safe_score_lower']))
 assert(F-2*N).overlaps(arb(d['simple_count_real_lower']));assert((F-N)/2).overlaps(arb(d['distinct_count_real_lower']))
 s=int(r['s1_lower']);nd=int(r['Nd_lower']);ss=int(r['s1_integer_refined_lower'])
 assert F-2*N>s-1 and(F-N)/2>nd-1
 assert all(F>3*k+4*((N-k)//2)for k in range(ss))
 assert not(F>3*ss+4*((N-ss)//2))
 assert Fraction(r['s1_fraction_rational'])==Fraction(s,N)and Fraction(r['Nd_fraction_rational'])==Fraction(nd,N)
 assert Fraction(r['s1_integer_refined_fraction_rational'])==Fraction(ss,N)
 assert sum((arb(x)for x in d['decomposition'].values()),arb(0)).overlaps(arb(d['frob_sq']))
 d300=d if m==300 else d300
assert d300['rational_inputs']['a_lower']==[8959,10]and d300['rational_inputs']['q_upper']==[5481,1]and d300['rational_inputs']['E_upper']==[25,2]and d300['rational_inputs']['N_upper']==185
assert len(d300['gates'])==8 and int(growth[0]['s1_lower'])==14 and int(growth[0]['Nd_lower'])==100 and int(growth[0]['s1_integer_refined_lower'])==15
for col in ['s1_fraction_rational','Nd_fraction_rational','s1_integer_refined_fraction_rational']:assert all(Fraction(a[col])<Fraction(b[col])for a,b in zip(growth,growth[1:]))
g=json.loads((P/'GATES.json').read_text());assert all(g[f'P{i}']for i in range(1,5))and not g['counterexample_found']and not g['B_C_interpretation_stopped']
for i in json.loads((P/'INPUTS.json').read_text())['inputs']:
 b=(P/i['file']).read_bytes();assert hashlib.sha256(b).hexdigest()==i['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==i['git_blob']
ref=json.loads((P/'C539_M300_COMPARISON.json').read_text());assert ref['max_abs_component_difference']<1e-10 and ref['MP_source_Frob2_point_inside_Arb']
files=set()
for line in(P/'SHA256SUMS').read_text().splitlines():
 h,n=line.split('  ',1);assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h,n;files.add(n)
assert {'RESULT.md','GATES.json','GROWTH.csv','arb_replay.py','verify.py'}<=files
print('PASS: all eight m300 gates, five Arb cells, rational scores/counts, integer refinement, source consistency, three input blobs and every SHA256')
