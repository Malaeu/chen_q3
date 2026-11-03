"""Sign-bracket checks of independently replayed LOW roots, no global root search.
Only the exact supplied decimal-vector model is enclosed, not spectral input error.
"""
from pathlib import Path
import sys,json,time,resource,hashlib,os
sys.path.insert(0,'/workspace/conditioning_deps')
from flint import arb,ctx
import mpmath as mp
resource.setrlimit(resource.RLIMIT_CPU,(15,15));ctx.prec=2000;mp.mp.dps=220
P=Path(__file__).resolve().parent;OUTPUT=Path(os.environ.get('GROUND_ROOT_BRACKET_OUTPUT',str(P/'low_bracket_validation_m300.json')));BASE=P.parent;rows=[];start=time.monotonic()
for w,parity in [('plant','odd'),('dh','odd'),('dh','even'),('plant','even'),('zeta','even')]:
 p=P/'results'/f'{w}_{parity}_m300.json';res=json.loads(p.read_text());source=Path(res['source_vector_path']);source=source if source.exists() else BASE/'spectra/vectors'/source.name;blob=source.read_bytes();assert hashlib.sha256(blob).hexdigest()==res['source_vector_sha256'];d=json.loads(blob);c=d['v_'+parity+'0_low'];m=300;degree=m if parity=='even' else m-1;L=mp.mpf(d['L_low']);Om=2*mp.pi*m/L;eps=mp.mpf('1e-100');aa=[arb(n)**2/(arb(m)**2) for n in range(1,m+1)];sq2=arb(2).sqrt();cc=[arb(s) for s in c]
 weights=[sq2*cc[n] for n in range(1,m+1)] if parity=='even' else [n*cc[n-1] for n in range(1,m+1)]
 lc=(cc[0] if parity=='even' else arb(0))+sum(weights,arb(0))
 def evaluate(x):
  return (cc[0] if parity=='even' else arb(0))+sum((weight*(x if parity=='even' else 1)/(x-a) for weight,a in zip(weights,aa)),arb(0))
 checks=[];centers=[]
 for q in res['precision_replay']['pairs']:
  z=mp.mpc(q['low_z_re'],q['low_z_im']);u=(z/Om)**2
  if abs(mp.im(u))>mp.mpf('1e-175'):checks.append(dict(root_id=q['root_id'],status='NONREAL_U_NOT_SIGN_BRACKETED'));continue
  center=mp.re(u);pole_free=min(abs(center-mp.mpf(n*n)/(m*m)) for n in range(1,m+1))>2*eps
  left=evaluate(arb(mp.nstr(center-eps,205)));right=evaluate(arb(mp.nstr(center+eps,205)));opposite=bool((left>0 and right<0) or (left<0 and right>0));centers.append(center)
  checks.append(dict(root_id=q['root_id'],u_center=mp.nstr(center,180),u_halfwidth='1e-100',pole_free=pole_free,opposite_endpoint_signs=opposite,status='PASS' if pole_free and opposite else 'FAIL'))
 ordered=sorted(centers);disjoint=all(y-x>2*eps for x,y in zip(ordered,ordered[1:]));passed=sum(x['status']=='PASS' for x in checks);leading_nonzero=bool(lc>0 or lc<0);complete=passed==degree and len(centers)==degree and disjoint and leading_nonzero
 row=dict(world=w,parity=parity,m=m,degree=degree,brackets_attempted=len(checks),passed=passed,all_brackets_disjoint=disjoint,leading_coefficient_proved_nonzero=leading_nonzero,complete_rounded_low_polynomial_real_root_census=complete,source_input_sha256=hashlib.sha256(blob).hexdigest(),arithmetic_bits=2000,checks=checks,scope='Opposite rigorous Arb endpoint signs on disjoint pole-free real-u brackets prove at least one rounded-vector rational-numerator root in each bracket. If their count equals the proven polynomial degree, these are all roots, all simple real-u. The supplied LOW coefficients are decimal constants; exact-ground spectral error is not enclosed.');rows.append(row)
 out=dict(seconds=time.monotonic()-start,rows=rows,scope='Bounded 15 CPU-second interval sign validation of low-vector replays; no source-zero seeds, no full far-root search.');tmp=OUTPUT.with_suffix('.tmp');tmp.write_text(json.dumps(out,indent=2)+'\n');tmp.replace(OUTPUT);print(w,parity,passed,degree,complete,flush=True)
