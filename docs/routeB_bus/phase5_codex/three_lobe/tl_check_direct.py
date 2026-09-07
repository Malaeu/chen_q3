"""Independent channel 1 (end-to-end, spatial): evaluate Q(f) for a concrete kernel
test f straight from the definition (C1) -- no block decomposition, no rho machinery,
no Delta bookkeeping -- and compare with c^T Q_7 c from the assembled matrix."""
import sys, time
import mpmath as mp, sympy as sp
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/three_lobe')
from tl_core import packet, phi_vals, gl_nodes, A, A_reg, A_tail
from tl_quad import flat_nodes

def direct_Q(coef9, P, Y='4.0', h='0.06', Nt=32, tpan=6, Nw=48, wpan=6):
    """coef9: list of 9 mpf, index 3p+j.  Returns dict with the pieces of (C1)."""
    d = P['delta']; half = d/2; C = P['centers']; cA = P['cA']
    def f(x):
        s = mp.mpf(0)
        for p in range(3):
            u = x - C[p]
            if abs(u) >= half: continue
            v = phi_vals(u, d)
            for j in range(3):
                s += coef9[3*p+j]*v[j]
        return s
    # quadrature nodes: union of the three lobes, flat map on each
    NODES, WTS = [], []
    for p in range(3):
        nn, ww = flat_nodes(C[p]-half, C[p]+half, Y, h)
        NODES += nn; WTS += ww
    FV = [f(x) for x in NODES]
    n = len(NODES)
    nrm  = sum(WTS[a]*FV[a]**2 for a in range(n))
    Mp   = sum(WTS[a]*FV[a]*mp.e**( NODES[a]/2) for a in range(n))
    Mm   = sum(WTS[a]*FV[a]*mp.e**(-NODES[a]/2) for a in range(n))
    def Rf(t):                                   # autocorrelation int f(x)f(x-t)dx
        return sum(WTS[a]*FV[a]*f(NODES[a]-t) for a in range(n))
    # D = int_0^inf A(t)*2*(Rf(0)-Rf(t)) dt, contact integrated as the cancelled form
    xt, wt = gl_nodes(Nt); D = mp.mpf(0)
    hh = d/tpan
    for pn in range(tpan):
        a0, b0 = hh*pn, hh*(pn+1); m_, r_ = (a0+b0)/2, (b0-a0)/2
        for x, w in zip(xt, wt):
            t = m_ + r_*x
            D += r_*w*(A_reg(t)+1/(2*t))*2*(nrm - Rf(t))
    Tmax = P['L3'] + d
    # breakpoints at the edges of the three correlation humps (lags log(3/2), log2, log3)
    lags = sorted([P['L3']-P['L2'], P['L2'], P['L3']])
    brk = [d]
    for Lg in lags: brk += [Lg-d, Lg+d]
    brk = sorted(set([b for b in brk if d <= b <= Tmax])) + [Tmax]
    xw, ww = gl_nodes(Nw)
    for a0, b0 in zip(brk[:-1], brk[1:]):
        m_, r_ = (a0+b0)/2, (b0-a0)/2
        if r_ <= 0: continue
        for x, w in zip(xw, ww):
            t = m_ + r_*x
            D += r_*w*A(t)*2*(nrm - Rf(t))
    D += 2*nrm*A_tail(Tmax)
    prime = mp.mpf(0); parts = {}
    for nn_, lam in ((2, mp.log(2)), (3, mp.log(3)), (4, mp.log(2)), (5, mp.log(5)),
                     (7, mp.log(7)), (8, mp.log(2)), (9, mp.log(3))):
        wn = lam/mp.sqrt(nn_); cf = Rf(mp.log(nn_))
        parts['C_f(log %d)' % nn_] = cf
        prime += -2*wn*cf
    Q = D - cA*nrm + prime + 2*Mp*Mm
    return dict(norm=nrm, D=D, arch=D-cA*nrm, prime=prime, pole=2*Mp*Mm, Q=Q,
                Mp=Mp, Mm=Mm, Cf=parts)

if __name__ == '__main__':
    import tl_analyze as TA
    from tl_kernel import kernel_basis
    t0 = time.time()
    mp.mp.dps = 40
    o = TA.run(dps=40)
    P = o['r']['P']; K = o['K']; Q7 = o['Q7']; G7 = o['G7']
    tests = {
        'z (mean direction)': [1,0,0,0,0,0,0],
        'mixed rational'    : [mp.mpf(3)/7, mp.mpf(-2)/5, 1, mp.mpf(4)/9,
                               mp.mpf('1e-3'), mp.mpf('-2e-3'), mp.mpf('5e-4')],
    }
    for name, c7 in tests.items():
        c7 = mp.matrix([[mp.mpf(x)] for x in c7])
        c9 = K*c7
        dd = direct_Q([c9[i] for i in range(9)], P)
        qm = (c7.T*Q7*c7)[0]; gm = (c7.T*G7*c7)[0]
        print('--- %s' % name)
        print('   ||f||^2  matrix %s   direct %s   rel %s' %
              (mp.nstr(gm,25), mp.nstr(dd['norm'],25), mp.nstr(abs(gm-dd['norm'])/abs(gm),3)))
        print('   Q        matrix %s   direct %s   rel %s' %
              (mp.nstr(qm,25), mp.nstr(dd['Q'],25), mp.nstr(abs(qm-dd['Q'])/abs(qm),3)))
        print('   split direct: D %s  arch %s  prime %s  pole %s' %
              tuple(mp.nstr(dd[k],18) for k in ('D','arch','prime','pole')))
        print('   C_f: ' + '  '.join('%s=%s' % (k, mp.nstr(v,6)) for k,v in dd['Cf'].items()))
        print('   M+ = %s  M- = %s' % (mp.nstr(dd['Mp'],8), mp.nstr(dd['Mm'],8)))
    print('elapsed %.1fs' % (time.time()-t0))
