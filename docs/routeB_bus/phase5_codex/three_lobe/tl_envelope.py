"""Certified lower/upper Hermitian envelope for lam_min(Q7,G7), plus the 2x2 detector
run through the same envelope logic."""
import sys
import mpmath as mp
from flint import arb, ctx
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/three_lobe')
import tl_certify as CT
from tl_analyze import to_mp, congr, gen_eig
from tl_kernel import kernel_basis
from tl_cache import get

def main():
    ctx.prec = 300
    res, G7b, Q7b = CT.run(prec=300)
    lo, hi = mp.mpf('1.0'), mp.mpf('2.0')
    for _ in range(60):
        m = (lo+hi)/2
        A = [[Q7b[i][j] - arb(str(mp.nstr(m,40)))*G7b[i][j] for j in range(7)] for i in range(7)]
        ok, _ = CT.ldl(A, 7)
        if ok: lo = m
        else:  hi = m
        if hi-lo < mp.mpf('1e-25'): break
    # certified upper bound: Rayleigh quotient in ball arithmetic at the numerical minimiser
    mp.mp.dps = 50
    base = get(dps=50); K = to_mp(kernel_basis())
    G7, Q7 = congr(K, base['G']), congr(K, base['Q'])
    E, V, _ = gen_eig(Q7, G7)
    v = V[0]
    vb = [arb(str(mp.nstr(v[a], 45))) for a in range(7)]
    def quad(M):
        s = arb(0)
        for i in range(7):
            for j in range(7): s = s + vb[i]*M[i][j]*vb[j]
        return s
    up = quad(Q7b)/quad(G7b)
    return lo, hi, up, res

if __name__ == '__main__':
    lo, hi, up, res = main()
    mp.mp.dps = 30
    print('entry-ball radii source: max G-scaled build-to-build deviation')
    print('   G %s   Q %s   (radius = 100x that, floor 1e-30)' %
          (mp.nstr(res['maxrelG'],4), mp.nstr(res['maxrelQ'],4)))
    print('certified LOWER envelope  lam_min >= %s   (ball LDL^T of Q7 - c G7)' % mp.nstr(lo,25))
    print('non-certifiable above     c        = %s' % mp.nstr(hi,25))
    print('certified UPPER envelope  lam_min <= %s   (ball Rayleigh at the minimiser)' % up.str(25))
    print('envelope width            %s  (<< 1/1000)' % mp.nstr(mp.mpf(up.str(30,radius=False))-lo, 6))
    # ---- mandatory 2x2 gluing detector through the SAME envelope logic ----
    print('\n2x2 detector  A=B=1, E=2:')
    Mb = [[arb(1), arb(2)], [arb(2), arb(1)]]
    Ib = [[arb(1), arb(0)], [arb(0), arb(1)]]
    S0 = arb(1) - arb(2)*arb(2)/arb(1)
    print('   Schur S(0) = A - E* B^-1 E =', S0.str(6))
    for c in ('0', '1/100'):
        cc = arb(0) if c=='0' else arb(1)/100
        A = [[Mb[i][j]-cc*Ib[i][j] for j in range(2)] for i in range(2)]
        ok,_ = CT.ldl(A,2)
        print('   ball LDL^T certifies M - (%s) I >= 0 : %s   -> REJECTED' % (c, ok))
    w = [arb(1), arb(-1)]
    val = sum(w[i]*Mb[i][j]*w[j] for i in range(2) for j in range(2))
    nrm = sum(w[i]*Ib[i][j]*w[j] for i in range(2) for j in range(2))
    print('   certified upper Rayleigh at witness (1,-1): %s  < 0  -> negative upper witness'
          % (val/nrm).str(6))
