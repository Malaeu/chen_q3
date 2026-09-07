"""Assemble the exact packet (C25): Gram G (9x9) and the complete polarized Weil form
(C1) = Arch + Prime + Pole on the nine generators f_ij = U_{x_i} phi_j.  Spatial route.

All bump integrals use the tanh-map trapezoid (both endpoints infinitely flat ->
doubly exponential decay -> spectral accuracy).  The t-integral of D uses composite
Gauss-Legendre on [0,delta] after the A(t) = 1/(2t) + A_reg(t) split, so the archimedean
contact at t=0 is integrated as the CANCELLED expression 2*sigma(0)-2*sigma(t) = O(t^2),
never as divergent pieces.
"""
import sys, time
import mpmath as mp
sys.path.insert(0, '/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/three_lobe')
from tl_core import packet, phi_vals, gl_nodes, A, A_reg, A_tail, eta_derivs
from tl_quad import flat_nodes, flat_quad

def build(dps=50, Y1='4.5', h1='0.02', Y2='4.0', h2='0.05',
          Nt=40, tpan=8, verbose=True):
    P = packet(dps)
    d = P['delta']; cA = P['cA']; C = P['centers']; half = d/2
    t0 = time.time()

    # ---------- 1D nodes on the full support -------------------------------
    U1, W1 = flat_nodes(-half, half, Y1, h1)
    PH1 = [[phi_vals(u, d)[j] for u in U1] for j in range(3)]
    g = mp.matrix(3,3)
    for j in range(3):
        for k in range(3):
            g[j,k] = sum(W1[a]*PH1[j][a]*PH1[k][a] for a in range(len(U1)))

    # ---------- rho_jk(t), rho_kj(t) on the exact overlap ------------------
    def rho_pair(t):
        lo, hi = -half, half - t
        if hi <= lo:
            z = mp.matrix(3,3); return z, z
        uu, ww = flat_nodes(lo, hi, Y2, h2)
        Pu = [[phi_vals(u,   d)[j] for u in uu] for j in range(3)]
        Pv = [[phi_vals(u+t, d)[j] for u in uu] for j in range(3)]
        R1 = mp.matrix(3,3); R2 = mp.matrix(3,3)
        n = len(uu)
        for j in range(3):
            for k in range(3):
                R1[j,k] = sum(ww[a]*Pu[j][a]*Pv[k][a] for a in range(n))
                R2[j,k] = sum(ww[a]*Pu[k][a]*Pv[j][a] for a in range(n))
        return R1, R2

    # ---------- diagonal block D_jk(0) -------------------------------------
    D0 = mp.matrix(3,3)
    xt, wt = gl_nodes(Nt)
    hh = d/tpan
    for p in range(tpan):
        a0 = hh*p; b0 = a0+hh; mm = (a0+b0)/2; rr = (b0-a0)/2
        for x, w in zip(xt, wt):
            t = mm + rr*x
            R1, R2 = rho_pair(t)
            fac = rr*w*(A_reg(t) + 1/(2*t))
            for j in range(3):
                for k in range(3):
                    D0[j,k] += fac*(2*g[j,k] - R1[j,k] - R2[j,k])
    tA = A_tail(d)
    for j in range(3):
        for k in range(3):
            D0[j,k] += 2*g[j,k]*tA
    if verbose: print('  diag block %.1fs' % (time.time()-t0))

    # ---------- cross blocks Theta_jk(Delta), Delta>0 ----------------------
    U2, W2 = flat_nodes(-half, half, Y2, h2)
    PH2 = [[phi_vals(u, d)[j] for u in U2] for j in range(3)]
    n2 = len(U2)
    def Theta(Delta):
        Am = [[A(Delta + U2[a] - U2[b]) for b in range(n2)] for a in range(n2)]
        M = mp.matrix(3,3)
        for j in range(3):
            for k in range(3):
                s = mp.mpf(0)
                for a in range(n2):
                    ca = W2[a]*PH2[j][a]
                    s += ca*sum(W2[b]*PH2[k][b]*Am[a][b] for b in range(n2))
                M[j,k] = -s
        return M
    L2, L3 = P['L2'], P['L3']
    Th = {str(D_): Theta(D_) for D_ in (L2, L3, L3-L2)}
    if verbose: print('  cross blocks %.1fs' % (time.time()-t0))

    # ---------- assemble 9x9 ----------------------------------------------
    idx = lambda p,j: 3*p+j
    Dm = mp.matrix(9,9); G = mp.matrix(9,9)
    for p in range(3):
        for q in range(3):
            Dl = C[p]-C[q]
            for j in range(3):
                for k in range(3):
                    if p == q:
                        Dm[idx(p,j), idx(q,k)] = D0[j,k]
                        G [idx(p,j), idx(q,k)] = g[j,k]
                    else:
                        M = Th[str(abs(Dl))]
                        Dm[idx(p,j), idx(q,k)] = M[j,k] if Dl > 0 else M[k,j]
    Arch = mp.matrix(9,9)
    for i in range(9):
        for jj in range(9):
            Arch[i,jj] = Dm[i,jj] - cA*G[i,jj]

    # ---------- prime part (general n loop; only n=2,3 can be active) ------
    def Lam(n):
        for pr in (2,3,5,7,11,13,17,19,23,29,31):
            m, e = n, 0
            while m % pr == 0: m //= pr; e += 1
            if e and m == 1: return mp.log(pr)
        return mp.mpf(0)
    Prime = mp.matrix(9,9); active = []; scanned = []
    for n in range(2, 40):
        lam = Lam(n)
        if lam == 0: continue
        wn = lam/mp.sqrt(n); ln = mp.log(n); hit = False
        for p in range(3):
            for q in range(3):
                Dl = C[p]-C[q]
                for sgn in (-1, +1):
                    s = Dl + sgn*ln
                    if abs(s) >= d: continue
                    hit = True
                    R1, R2 = rho_pair(abs(s))
                    for j in range(3):
                        for k in range(3):
                            val = R1[j,k] if s >= 0 else R2[j,k]
                            Prime[idx(p,j), idx(q,k)] -= wn*val
        scanned.append((n, float(ln), hit))
        if hit: active.append((n, wn))

    # ---------- pole part --------------------------------------------------
    m_eta = flat_quad(lambda x: eta_derivs(x,d,0)[0]*mp.cosh(x/2), -half, half, Y1, h1)
    Mmom = [[flat_quad(lambda x, j=j, sg=sg: phi_vals(x,d)[j]*mp.e**(sg*x/2),
                       -half, half, Y1, h1) for sg in (1,-1)] for j in range(3)]
    rp = [mp.mpf(0)]*9; rm = [mp.mpf(0)]*9
    for p in range(3):
        s_ = mp.e**(C[p]/2)
        for j in range(3):
            rp[idx(p,j)] = s_   * (1 if j==0 else (mp.mpf(-1)/2 if j==1 else 0))
            rm[idx(p,j)] = (1/s_)*(1 if j==0 else (mp.mpf( 1)/2 if j==1 else 0))
    Pole = mp.matrix(9,9)
    for i in range(9):
        for jj in range(9):
            Pole[i,jj] = m_eta**2*(rp[i]*rm[jj] + rm[i]*rp[jj])

    Q = mp.matrix(9,9)
    for i in range(9):
        for jj in range(9):
            Q[i,jj] = Arch[i,jj] + Prime[i,jj] + Pole[i,jj]

    rt = time.time()-t0
    if verbose: print('  total %.1fs' % rt)
    return dict(P=P, g=g, G=G, D=Dm, Arch=Arch, Prime=Prime, Pole=Pole, Q=Q,
                m_eta=m_eta, Mmom=Mmom, active=active, scanned=scanned,
                rp=rp, rm=rm, D0=D0, Th=Th, runtime=rt)

if __name__ == '__main__':
    import pickle
    r = build()
    with open('/home/chirurgie/.claude/jobs/4b35770d/tmp/three_lobe/build.pkl','wb') as f:
        pickle.dump({k: (mp.nstr(v, 45) if isinstance(v, mp.mpf) else v)
                     for k,v in [('runtime', r['runtime'])]}, f)
    mp.mp.dps = 30
    print('delta', r['P']['delta']); print('m_eta', r['m_eta'])
    print('active primes', [(n, mp.nstr(w,12)) for n,w in r['active']])
    print('inactive scanned n (log n vs support diam %s):' % mp.nstr(r['P']['L3']+r['P']['delta'],10),
          [n for n,l,h in r['scanned'] if not h][:8])
    print('g'); print(r['g'])
    print('D0'); print(r['D0'])
