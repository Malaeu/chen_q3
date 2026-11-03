"""CANDIDATE ONLY: LOW-point ground refinement seeded by ordered HIGH pair.

HIGH still uses full native ordering. LOW lambda1 and vector1 are NOT computed.
No RH/positivity premise; correspondence uses the measured matrix perturbation.
"""
import time,math
import gmpy2 as g
from flint import arb,arb_mat,fmpq,ctx
F=g.mpfr

def refine(A,low_bits,B,high_bits,high):
    if high_bits!=high['bits']:raise ValueError('HIGH point precision must equal actual HIGH solver bits')
    start=time.monotonic();cpu=time.process_time();old_gp=g.get_context().precision;old_flint=ctx.prec
    work_bits=low_bits+72
    try:
        g.get_context().precision=max(old_gp,high_bits+80);ctx.prec=work_bits
        n=len(A);AL=[[g.mpfr(x,low_bits) for x in row] for row in A];AH=[[g.mpfr(x,high_bits) for x in row] for row in B]
        entry=max(abs(x-y) for ar,br in zip(AL,AH) for x,y in zip(ar,br));op=n*entry
        scale=max(F(1),max(abs(x) for row in AH for x in row));high_round=F(2)**(-high_bits+24)*scale
        hierr=g.sqrt(n)*max(high['residual_infinity'])+high_round;radius=op+hierr
        gap=high['lambda'][1]-high['lambda'][0];shift=high['lambda'][0]-gap/128;shift_margin=gap/128-radius
        if not (gap>0 and radius<gap/1024 and shift_margin>0):raise ArithmeticError('LOW/HIGH ground correspondence or shift gate unresolved')
        def point(x):return arb(fmpq(*map(int,x.as_integer_ratio())))
        M=arb_mat([[point(x) for x in row] for row in AL]);s=point(shift)
        C=M-arb_mat(n,n,[s if i==j else 0 for i in range(n) for j in range(n)])
        seed=arb_mat([[point(x)] for x in high['v'][0]])
        seedlam=(seed.transpose()*M*seed)[0,0]/(seed.transpose()*seed)[0,0]
        seedres=M*seed-seed*seedlam;initial=max(abs(seedres[i,0]).upper() for i in range(n))
        converted=time.process_time();w=C.solve(seed,algorithm='approx');norm=(w.transpose()*w)[0,0].sqrt()
        v=arb_mat([[(w[i,0]/norm).mid()] for i in range(n)]);Mv=M*v
        lam=((v.transpose()*Mv)[0,0]/(v.transpose()*v)[0,0]).mid();res=Mv-v*lam
        residual=max(abs(res[i,0]).upper() for i in range(n));digits=math.ceil(work_bits*math.log10(2))+8
        def mid(x):return F(x.mid().str(digits,radius=False))
        vv=[mid(v[i,0]) for i in range(n)];la=mid(lam);rr=mid(residual)
        if sum((x*y for x,y in zip(vv,high['v'][0])),F(0))<0:vv=[-x for x in vv]
        initial_gp=mid(initial);round_floor=F(2)**(-work_bits+24)*scale
        if not rr<max(initial_gp/32,round_floor):raise ArithmeticError('LOW shifted solve did not improve the seed residual enough')
        if not (rr<radius/16 and abs(la-high['lambda'][0])<gap/8):raise ArithmeticError('LOW refined ground residual/location gate failed')
        return dict(method='LOW_POINT_SHIFTED_REAL_ARB_REFINEMENT_FROM_ORDERED_HIGH',bits=low_bits,arithmetic_bits=work_bits,lambda_=[la,None],v=[vv,None],residual_infinity=[rr,None],seconds=time.process_time()-cpu,wall_seconds=time.monotonic()-start,conversion_CPU_seconds=converted-cpu,solve_checks_CPU_seconds=time.process_time()-converted,point_entry_difference=entry,point_operator_difference=op,weyl_radius=radius,lambda1_status='NOT_COMPUTED; EMPIRICAL_POINT_MATRIX_WEYL_BOUND_FROM_ORDERED_HIGH',lambda1_weyl_interval=[high['lambda'][1]-radius,high['lambda'][1]+radius],shift=shift,shift_below_low_ground_margin=shift_margin,initial_residual=initial_gp,correspondence_gate=True,certificate=False)
    finally:
        g.get_context().precision=old_gp;ctx.prec=old_flint
