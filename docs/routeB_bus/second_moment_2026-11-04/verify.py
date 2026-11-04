"""Offline scalar conservation, census, score and packet integrity checks."""
from pathlib import Path
from collections import defaultdict
import csv,json,math,hashlib
P=Path(__file__).resolve().parent
def rows(n):return list(csv.DictReader((P/n).open()))
def near(a,b,rel=1e-11):assert abs(a-b)<=rel*max(1,abs(a),abs(b)),(a,b)
s=rows('SUMMARY.csv');src=rows('SOURCE_MOMENTS.csv');d=rows('DECOMPOSITION.csv')
assert len(s)==5130 and len(src)==855 and len(d)==9405
assert len({(r['world'],r['m'],r['cutoff'],r['sigma_convention'])for r in s})==5130
D=defaultdict(list)
for r in d:D[r['world'],r['m']].append(float(r['value']))
S={(r['world'],r['m']):r for r in src};assert len(S)==855
for key,r in S.items():
 assert int(r['dimension'])==int(r['m'])+1 and int(r['source_bits'])==400 and int(r['GL_order'])==192 and int(r['panels'])==8
 assert len(D[key])==11;near(math.fsum(D[key]),float(r['Frob2']),1e-12)
 assert float(r['arithmetic_atom_reconstruction_maxerr'])<2e-12
 assert r['endpoint_atom_exact_zero']=='True'
counts={}
for r in s:
 w,m=r['world'],r['m'];F=float(r['Frob2']);sigma=float(r['sigma']);N=int(r['N_upper_with_multiplicity']);line=int(r['N_on_line_simple']);h=int(r['N_distinct_heights']);tr=float(r['trace']);v=F/(sigma*sigma*N)
 assert N==line+2*(h-line) and int(r['N_distinct_complex'])==N
 near(F,float(S[w,m]['Frob2']));near(tr,float(S[w,m]['trace']));near(v,float(r['v']));near(2-v,float(r['raw_simple_lower']));near((3-v)/2,float(r['raw_distinct_lower']))
 phi=(4*tr/sigma-F/sigma**2)/N;near(phi-2,float(r['finite_unpaid_simple_score']));near((phi-1)/2,float(r['finite_unpaid_distinct_score']))
 L=math.log(int(m));kap=1+(1+math.log(L))/(4*L)if r['cutoff']=='primary'else 1.;near(kap,float(r['kappa']));near(kap*2*math.pi*int(m)/L,float(r['T']));near(L/(L-math.log(L)+math.log(kap)),float(r['lambda_eff']))
 tol=float(r['sanity_tolerance']);viol=2-v>line/N+tol or(3-v)/2>1+tol
 assert (r['raw_sanity_pass']=='True')==(not viol)
 assert r['convention_interpretation_stopped']=='True'
 counts[w,m,r['cutoff']]=N
for m in range(16,301):
 for c in ['primary','kappa1']:assert counts['plant',str(m),c]==counts['zeta',str(m),c]+2
for w,N in [('zeta',183),('dh',276),('plant',185)]:assert counts[w,'300','primary']==N
assert all(r['pass_gate']=='True'for r in rows('PRIMARY_CENSUS_GATE.csv')) and len(rows('PRIMARY_CENSUS_GATE.csv'))==855
assert all(r['pass_gate']=='True'for r in rows('normalization_check.csv'))
sharp=rows('sigma_sharp.csv');assert len(sharp)==285
for r in sharp:assert float(r['L'])<=float(r['sigma_sharp'])<=float(r['sigma_L_plus_inverse_gamma'])+1e-13
sc=json.loads((P/'SCORES.json').read_text());assert not sc['V1_pass'] and sc['V2_pass'] and not sc['V3_pass'] and not sc['V4_pass']
assert all(sc['stopped_conventions'].values())
for line in (P/'SHA256SUMS').read_text().splitlines():
 expected,name=line.split('  ',1);assert hashlib.sha256((P/name).read_bytes()).hexdigest()==expected,name
print('PASS: 855 moments, 9405 decomposition terms, 5130 scores, census gates, conditional caps, stop flags and all packet hashes')
