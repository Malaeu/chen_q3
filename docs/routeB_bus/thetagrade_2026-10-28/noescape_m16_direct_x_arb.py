#!/usr/bin/env python3
"""Direct physical m16 X via Arb gamma integrals; no use of F+X identity.

One finite cell. Analytic omitted-tail budgets require the accompanying audit.
No asynchronous signal handlers are used inside Arb callbacks.
"""
import hashlib,json,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
from flint import arb,acb,ctx
from noescape_m16_direct_x import normalized_arb_input
HERE=Path(__file__).resolve().parent
INPUT=HERE/'noescape_m16_eigenpair.json'
DENOM=HERE/'noescape_m16_direct_x.json'
OUTPUT=HERE/'noescape_m16_direct_x_arb.json'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rec(x):
    x=arb(x)
    return {'ball':str(x),'lower':str(x.lower()),'upper':str(x.upper())}

def main():
    ctx.dps=70;ctx.threads=1
    started=time.monotonic()
    data=json.loads(INPUT.read_text());old=json.loads(DENOM.read_text())
    assert old['input_sha256']==sha(INPUT)
    unit,_,_,lam=normalized_arb_input(data)
    assert abs(lam)<1
    B=arb(old['input']['B_abs_lambda_times_overlap']['ball'])
    assert B>0
    L=arb(16).log();b=L/2;pi=arb.pi();sq=L.sqrt();delta=arb('1e-24');S=L+arb('.4')
    out={'status':'RUNNING_NOT_CERTIFIED','input_sha256':sha(INPUT),'denominator_sha256':sha(DENOM),'script_sha256':sha(Path(__file__)),'dps':ctx.dps,'formula':'X=k(hout,v)-k(W,v)+lambda<W,v>; independent of F','parts':[]}
    def save():
        out['seconds']=round(time.monotonic()-started,3)
        OUTPUT.write_text(json.dumps(out,indent=2)+'\n')
    def params(k):
        p=(acb(arb('4.5'))+k)/2;q=(acb(arb('2.5'))+k)/2
        return p,q,8*pi*pi*acb(pi)**(-p),-12*pi*acb(pi)**(-q)
    def primitive(y,P):
        p,q,A,C=P;z=pi*(2*y).exp()
        return A*acb(z).gamma_upper(p)+C*acb(z).gamma_upper(q)
    rows=[]
    for r in range(-16,17):
        k=acb(0,2*pi*r/L);P=params(k);M=params(-k)
        rows.append((unit[r+16],k,P,M,primitive(acb(b),P),primitive(acb(3*b),M)))
    def qW(s):
        return 2/sq*sum((c*(k*(s+b)).exp()*(primitive(b+s,M)-at3b+atb-primitive(3*b-s,P)) for c,k,P,M,atb,at3b in rows),acb(0))
    def qH(s,upper):
        return 2/sq*sum((c*(k*(b-s)).exp()*((primitive(s-b,P) if upper else atb)-primitive(s+b,P)) for c,k,P,M,atb,at3b in rows),acb(0))
    q0=qW(acb(0));inner=q0/2
    out['qW_zero']=str(q0)
    count=0
    def callback(kind):
        def fun(s,analytic):
            nonlocal count
            count+=1
            # Conservative analytic subdomain. exp(2(b+s)) stays away from
            # the incomplete-gamma branch cut throughout these complex balls.
            if not s.imag.abs_upper()<arb('.12') or not s.real>arb('-.01') or not s.real<S+arb('.01'):
                return acb('nan')
            j=(-s/2).exp()/(-(-2*s).expm1())
            return j*((q0-qW(s)) if kind=='W' else qH(s,kind=='H_upper'))
        return fun
    def integral(kind,points):
        total=acb(0)
        for a,z in zip(points,points[1:]):
            val=acb.integral(callback(kind),a,z,abs_tol=arb('1e-37'),rel_tol=arb('1e-18'),eval_limit=20000,depth_limit=30)
            if not val.is_finite():raise ArithmeticError(f'nonfinite {kind} integral')
            total+=val
            out['parts'].append({'kind':kind,'a':str(a),'b':str(z),'ball':str(val)})
            save()
            print(kind,len(out['parts']),str(val),'seconds',round(time.monotonic()-started,1),flush=True)
        return total
    try:
        points=sorted([delta,arb('.01'),arb('.05'),arb('.15')]+[L*i/16 for i in range(1,17)],key=lambda x:float(x.mid()))
        AW=integral('W',points)
        AH=integral('H_lower',points)+integral('H_upper',[L+(S-L)*i/4 for i in range(5)])
        def J(a,z,k):
            P=params(acb(k));return primitive(acb(a),P)-(primitive(acb(z),P) if z is not None else acb(0))
        pp_v=sum((c*arb(2).sqrt()*(b/2).sinh()/(sq*(arb('.25')+(2*pi*r/L)**2)) for r,c in zip(range(-16,17),unit)),arb(0))
        pp_H=arb(2).sqrt()*(J(b,None,arb('.5'))+J(b,None,arb('-.5')))
        pp_W=arb(2).sqrt()*((L/2).exp()*J(b,3*b,arb('-.5'))+(-L/2).exp()*J(b,3*b,arb('.5')))
        def mang(n):
            for p in range(2,n+1):
                if any(p%d==0 for d in range(2,int(p**.5)+1)):continue
                q=n
                while q%p==0:q//=p
                if q==1:return arb(p).log()
            return arb(0)
        PH=acb(0);PW=acb(0)
        for n in range(2,65):
            weight=mang(n)/arb(n).sqrt()
            if weight==0:continue
            s=arb(n).log()
            PH+=weight*qH(acb(s),n>16)
            if n<16:PW+=weight*qW(acb(s))
            # qW(L)=0 exactly. n=16 is retained in PH, zero in PW.
        cstar=arb.const_euler()+(8*pi).log()+pi/2
        JL=arb('0.5')*(arb(5)/3).log()+arb('.25').atan()
        kH=-AH-PH+pp_H*pp_v
        kW=-cstar*inner+AW+q0*JL-PW+pp_W*pp_v
        X=kH-kW+lam*inner
        # Near-zero integrals: W1<3e-17, |v|<4, |v'|<80, L<3,
        # sup|qW'|<2e-14, and s*j(s)<1 on [0,delta].
        near=arb('2.1e-38')
        u=(-S/2).exp();JS=((1+u)/(1-u)).log()/2+u.atan()
        arch_tail=2*sq*1000*(arb('4.5')*(S-b)-pi*(2*(S-b)).exp()).exp()*JS
        n=arb(65);a=pi/16;ratio=((n+1)/n)**5*(-a*(2*n+1)).exp()
        assert ratio<1
        prime_tail=2*sq*1000*arb(16)**(-arb('2.25'))*n.log()*n**4*(-a*n*n).exp()/(1-ratio)
        # Full proof of the deliberately loose 1e-60 replacement budget is
        # required in the companion audit; never inferred from a first term.
        replacement=arb('1e-60')
        tail=near+arch_tail+prime_tail+replacement
        full=arb(X.real.mid(),X.real.rad()+tail.abs_upper())
        out.update({'status':'COMPUTED_PENDING_INDEPENDENT_TAIL_AND_SOURCE_REVIEW','qW_zero':str(q0),'W_inner':str(inner),'W_arch':str(AW),'H_arch':str(AH),'W_prime':str(PW),'H_prime':str(PH),'p_v':str(pp_v),'p_H':str(pp_H),'p_W':str(pp_W),'k_H1':str(kH),'k_W1':str(kW),'X_truncated':str(X),'near_zero_budget':rec(near),'arch_far_tail_budget':rec(arch_tail),'prime_far_tail_budget':rec(prime_tail),'replacement_budget_pending_review':rec(replacement),'X_with_all_proposed_budgets':rec(full),'B':rec(B),'abs_X_over_B_upper':str((abs(full)/B).upper()),'quarter_test':bool(abs(full)<B/4),'evals':count,'note':'Conditional on analytic budgets and inherited certified eigenpair/B; finite m16 only, no NOESCAPE/RH conclusion.'})
        assert 0 in X.imag
        print('FINAL',out['X_with_all_proposed_budgets'],out['abs_X_over_B_upper'],out['quarter_test'],flush=True)
    except Exception as e:
        out['status']='INCOMPLETE';out['error']=repr(e);raise
    finally:save()
if __name__=='__main__':main()
