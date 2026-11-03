"""Validated real-u secular continuation for exact decimal-vector numerators.
No source-zero seeds. Every gate is mandatory; callers must fall back on failure.
"""
from pathlib import Path
from fractions import Fraction
import json,hashlib,time,sys
sys.path.insert(0,'/workspace/conditioning_deps')
import gmpy2 as g
from flint import arb,acb,acb_poly,ctx
from bisect import bisect_left

HELPER_SHA256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

class ContinuationUnavailable(ValueError):pass

def isolate_real(c,m,parity,previous_path,current_source_path=None,bits=None,expected_source_sha256=None):
    if parity!='even':raise ContinuationUnavailable('Fast path restricted to even parity')
    start=time.monotonic();cpu=time.process_time();bits=bits or max(1000,5*m+500);ctx.prec=bits;g.get_context().precision=bits
    previous_path=Path(previous_path);previous_blob=previous_path.read_bytes();prev=json.loads(previous_blob)
    if int(prev['m'])!=m-1 or prev['parity']!=parity:raise ContinuationUnavailable('Previous dimension/parity mismatch')
    previous_source_blob=Path(prev['source_vector_path']).read_bytes()
    if hashlib.sha256(previous_source_blob).hexdigest()!=prev['source_vector_sha256']:raise ContinuationUnavailable('Stale previous source receipt')
    previous_source=json.loads(previous_source_blob)
    if previous_source['m']!=m-1 or previous_source.get('N',m-1)!=m-1 or previous_source['world']!=prev['world']:raise ContinuationUnavailable('Previous source metadata mismatch')
    if not previous_source.get('even_ground_resolved'):raise ContinuationUnavailable('Previous even ground unresolved')
    if current_source_path is not None:
        source_blob=Path(current_source_path).read_bytes();source=json.loads(source_blob)
        if source['world']!='zeta':raise ContinuationUnavailable('Fast path restricted to zeta world')
        if expected_source_sha256 is not None and hashlib.sha256(source_blob).hexdigest()!=expected_source_sha256:raise ContinuationUnavailable('Current source changed after caller snapshot')
        if source.get('N',m)!=m or not source.get('even_ground_resolved'):raise ContinuationUnavailable('Current even carrier/ground metadata mismatch')
        if source['m']!=m or source['world']!=prev['world']:raise ContinuationUnavailable('Current world/dimension mismatch')
        actual=source['v_even0'] if parity=='even' else source['v_odd0']
        if actual!=c:raise ContinuationUnavailable('Current coefficients differ from frozen input')
    else:raise ContinuationUnavailable('Current source path required for continuation receipt')
    roots=[r for r in prev['roots'] if r['kind'].startswith('polynomial')]
    expected=m if parity=='even' else m-1
    if len(roots)!=expected-1 or any(g.mpfr(r['u_im'])!=0 for r in roots):raise ContinuationUnavailable('Previous root set not complete real-u')
    F=g.mpfr;zero=F(0);one=F(1);aa=[F(n*n)/F(m*m) for n in range(1,m+1)];cc=list(map(F,c));weights=[g.sqrt(F(2))*v for v in cc[1:]] if parity=='even' else [F(n)*cc[n-1] for n in range(1,m+1)]
    leading=(cc[0] if parity=='even' else zero)+sum(weights,zero)
    if not leading:raise ContinuationUnavailable('Zero numerical leading coefficient')
    residues=[w*a for w,a in zip(weights,aa)] if parity=='even' else weights
    constant=leading if parity=='even' else zero
    tolerance=F('1e-190')
    def refine(seed):
        u=seed
        for it in range(16):
            value=constant;derivative=zero
            for residue,a in zip(residues,aa):
                den=u-a
                if not den:raise ContinuationUnavailable('Newton hit a pole')
                term=residue/den;value+=term;derivative-=term/den
            if not derivative:raise ContinuationUnavailable('Zero numerical Newton derivative')
            du=value/derivative;u-=du
            if abs(du)<tolerance*max(one,abs(u)):return u,it+1
        raise ContinuationUnavailable('Newton did not converge')
    scale=(F(m-1)*F(source['L'])/(F(m)*F(prev['L'])))**2
    refined=[];steps=[];seed_failures=[]
    lattice_scale=(F(m-1)/F(m))**2;far_scale=(F(m)/F(m-1))**2
    for index,r in enumerate(roots):
        base=F(r['u_re'])
        scales=[scale,lattice_scale]+([far_scale] if abs(base)>one else [])
        for strategy,seed_scale in enumerate(scales):
            try:u,it=refine(base*seed_scale);refined.append(u);steps.append(it)
            except ContinuationUnavailable as e:seed_failures.append(dict(index=index,strategy=strategy,error=str(e)))
    refined.sort();known=[]
    for u in refined:
        if not known or abs(u-known[-1])>=F('1e-120')*max(one,abs(u),abs(known[-1])):known.append(u)
    duplicates=len(refined)-len(known);missing_count=expected-len(known)
    if not 0<=missing_count<=4:raise ContinuationUnavailable('More than four missing continued roots')
    # Recover missing roots from top coefficients / Newton power-sum identities.
    # This step supplies seeds only; the independent interval gate below proves every root.
    k=missing_count;dc=[one]+[zero]*k
    for a in aa:
        for j in range(k,0,-1):dc[j]-=a*dc[j-1]
    if parity=='even':
        moments=[sum((w*a**(l+1) for w,a in zip(weights,aa)),zero) for l in range(k)]
        top=[leading]+[leading*dc[j]+sum((moments[l-1]*dc[j-l] for l in range(1,j+1)),zero) for j in range(1,k+1)]
    else:
        moments=[sum((w*a**l for w,a in zip(weights,aa)),zero) for l in range(k+1)]
        top=[sum((moments[l]*dc[j-l] for l in range(j+1)),zero) for j in range(k+1)]
    monic=[v/leading for v in top];power=[zero]*(k+1);missing_power=[zero]*(k+1);small=[one]+[zero]*k
    for j in range(1,k+1):
        power[j]=-F(j)*monic[j]-sum((monic[i]*power[j-i] for i in range(1,j)),zero)
        missing_power[j]=power[j]-sum((u**j for u in known),zero)
        small[j]=-(missing_power[j]+sum((small[i]*missing_power[j-i] for i in range(1,j)),zero))/F(j)
    small_poly=acb_poly([arb(str(v)) for v in reversed(small)])
    seeds=small_poly.roots(tol=arb('1e-195'),maxprec=bits*2) if k else []
    refined=list(known)
    for seed in seeds:
        if not seed.imag.contains(0):raise ContinuationUnavailable('Missing-root seed is nonreal')
        u,it=refine(F(seed.real.mid().str(bits//3,radius=False)));refined.append(u);steps.append(it)
    refined.sort()
    if any(abs(b-a)<F('1e-120')*max(one,abs(a),abs(b)) for a,b in zip(refined,refined[1:])):raise ContinuationUnavailable('Missing-root duplicate')
    # Independent interval signs for the exact supplied decimal coefficient model.
    ca=list(map(arb,c));ar=[arb(n)**2/arb(m)**2 for n in range(1,m+1)];wa=[arb(2).sqrt()*v for v in ca[1:]] if parity=='even' else [n*ca[n-1] for n in range(1,m+1)];lc=(ca[0] if parity=='even' else arb(0))+sum(wa,arb(0))
    if not (lc>0 or lc<0):raise ContinuationUnavailable('Leading coefficient interval contains zero')
    ra=[w*a for w,a in zip(wa,ar)] if parity=='even' else wa;constant_a=lc if parity=='even' else arb(0)
    def evaluate(x):return constant_a+sum((r/(x-a) for r,a in zip(ra,ar)),arb(0))
    eps=F('1e-167');quarter=eps/4;intervals=[];balls=[];sign_records=[];poles=[Fraction(n*n,m*m) for n in range(1,m+1)]
    for u in refined:
        left_s,right_s=str(u-quarter),str(u+quarter);lo,hi=Fraction(left_s),Fraction(right_s)
        pole_index=bisect_left(poles,lo)
        if not lo<hi or (pole_index<len(poles) and poles[pole_index]<=hi):raise ContinuationUnavailable('Bracket intersects an internal pole')
        if intervals and not intervals[-1][1]<lo:raise ContinuationUnavailable('Overlapping exact brackets')
        left,right=evaluate(arb(left_s)),evaluate(arb(right_s))
        if not ((left>0 and right<0) or (left<0 and right>0)):raise ContinuationUnavailable('Opposite interval endpoint signs not established')
        ball=arb(str(u)+' +/- 1e-167')
        if not ball.contains(arb(left_s)) or not ball.contains(arb(right_s)):raise ContinuationUnavailable('Output ball does not enclose checked endpoints')
        if balls and not balls[-1].real<ball:raise ContinuationUnavailable('Output root balls overlap')
        if not ball.rad()<arb('1e-165'):raise ContinuationUnavailable('Output radius exceeds declared isolation target')
        balls.append(acb(ball,0));intervals.append((lo,hi));sign_records.append(dict(left=left_s,right=right_s,left_sign=1 if left>0 else -1,right_sign=1 if right>0 else -1))
    if len(balls)!=expected:raise ContinuationUnavailable('Degree accounting failed')
    info=dict(producer_sha256=HELPER_SHA256,method='MPFR secular continuation + Vieta/Newton-power-sum missing roots + Arb signs/exact rational disjoint pole-free brackets + degree',bits=bits,degree=expected,isolated_count=len(balls),seconds=time.monotonic()-start,cpu_seconds=time.process_time()-cpu,prior_failures=[],newton_max_steps=max(steps),previous_seed_failures=seed_failures,previous_seed_duplicates=duplicates,missing_root_count=missing_count,previous_result_path=str(previous_path),previous_result_sha256=hashlib.sha256(previous_blob).hexdigest(),previous_source_sha256=prev['source_vector_sha256'],current_source_sha256=hashlib.sha256(source_blob).hexdigest(),leading_coefficient_ball=lc.str(40),output_u_radius_target='1e-167',required_u_radius_upper='1e-165',brackets=sign_records,scope='Complete isolation of the frozen supplied decimal-vector numerator only. Degree-many disjoint real-u sign brackets imply all roots, each simple. Source/ground uncertainty is not enclosed.')
    return balls,info
