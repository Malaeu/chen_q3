"""Certified sign statement.  Entry enclosures (balls) -> exact kernel restriction in ball
arithmetic -> LDL^T positivity certificates.  Everything downstream of the entry balls is
rigorous (python-flint / Arb ball arithmetic); the entry radii themselves come from the
quadrature-refinement ledger and are stated as such."""
import sys
import mpmath as mp
from flint import arb, ctx
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/three_lobe')

def cert_pos(x):
    return bool(x > 0)

def ldl(Ab, n):
    """LDL^T of a symmetric ball matrix (list of lists of arb). Returns (ok, pivots)."""
    L = [[arb(0)]*n for _ in range(n)]
    d = [arb(0)]*n
    for i in range(n):
        s = Ab[i][i]
        for k in range(i): s = s - L[i][k]*L[i][k]*d[k]
        d[i] = s
        if not cert_pos(d[i]): return False, d
        L[i][i] = arb(1)
        for j in range(i+1, n):
            t = Ab[j][i]
            for k in range(i): t = t - L[j][k]*L[i][k]*d[k]
            L[j][i] = t/d[i]
    return True, d

def ball_mat(M, R, n=9):
    return [[arb(str(mp.nstr(M[i,j], mp.mp.dps)), str(R[i][j])) for j in range(n)] for i in range(n)]

def kernel_arb():
    s2, s3 = arb(2).sqrt(), arb(3).sqrt()
    h = arb(1)/2
    def vec(a,b,c):
        out=[]
        for p in range(3): out += [a[p], b[p], c[p]]
        return out
    def from_uv(u,v):
        a=[(u[p]+v[p])/2 for p in range(3)]; b=[v[p]-u[p] for p in range(3)]
        return vec(a,b,[arb(0)]*3)
    z=[arb(-1), 2*s2, -s3]; Z=[arb(0)]*3
    cols=[vec(z,Z,Z), from_uv([s2,arb(-1),arb(0)],Z), from_uv([s3,arb(0),arb(-1)],Z),
          from_uv(Z,[arb(1),-s2,arb(0)]),
          vec(Z,Z,[arb(1),arb(0),arb(0)]), vec(Z,Z,[arb(0),arb(1),arb(0)]),
          vec(Z,Z,[arb(0),arb(0),arb(1)])]
    return [[cols[c][i] for c in range(7)] for i in range(9)]   # 9x7

def congr(K, M, n=9, m=7):
    T=[[arb(0)]*m for _ in range(n)]
    for i in range(n):
        for b in range(m):
            s=arb(0)
            for j in range(n): s = s + M[i][j]*K[j][b]
            T[i][b]=s
    out=[[arb(0)]*m for _ in range(m)]
    for a in range(m):
        for b in range(m):
            s=arb(0)
            for i in range(n): s = s + K[i][a]*T[i][b]
            out[a][b]=s
    return out

def run(prec=300):
    from tl_cache import get
    ctx.prec = prec
    base = get(dps=50)
    var  = get(dps=60, Y1='5.0', h1='0.015', Y2='4.2', h2='0.035', Nt=56, tpan=12)
    mp.mp.dps = 50
    G, Q = base['G'], base['Q']
    dev = {'G': mp.matrix(9,9), 'Q': mp.matrix(9,9)}
    for nm in ('G','Q'):
        for i in range(9):
            for j in range(9):
                dev[nm][i,j] = abs(base[nm][i,j] - var[nm][i,j])
    sc = [mp.sqrt(G[i,i]) for i in range(9)]
    maxrelG = max(dev['G'][i,j]/(sc[i]*sc[j]) for i in range(9) for j in range(9))
    maxrelQ = max(dev['Q'][i,j]/(sc[i]*sc[j]) for i in range(9) for j in range(9))
    SAFE = 100
    RG = [[max(dev['G'][i,j]*SAFE, sc[i]*sc[j]*mp.mpf('1e-30')) for j in range(9)] for i in range(9)]
    RQ = [[max(dev['Q'][i,j]*SAFE, sc[i]*sc[j]*mp.mpf('1e-30')) for j in range(9)] for i in range(9)]
    Gb, Qb = ball_mat(G, RG), ball_mat(Q, RQ)
    K = kernel_arb()
    G7, Q7 = congr(K, Gb), congr(K, Qb)
    res = {'maxrelG': maxrelG, 'maxrelQ': maxrelQ}
    okG, dG = ldl(G7, 7); res['G7_pd'] = okG
    for c in ('1/100', '1', '3/2', '17/10', '1.744', '1.745'):
        cc = arb(int(c.split('/')[0]))/int(c.split('/')[1]) if '/' in c else arb(c)
        A = [[Q7[i][j] - cc*G7[i][j] for j in range(7)] for i in range(7)]
        ok, dd = ldl(A, 7)
        res['floor_'+c] = ok
    # rigorous G-norm radius of the entry errors, in the G-orthonormal frame:
    # ||E||_G <= || L^{-1} E L^{-T} ||_F ; bound it by sum_ij r_ij / sqrt(G7_ii G7_jj) (crude, valid)
    return res, G7, Q7

if __name__ == '__main__':
    res, G7, Q7 = run()
    mp.mp.dps = 20
    print('max G-scaled entry deviation between the two builds:')
    print('   G: %s   Q: %s' % (mp.nstr(res['maxrelG'],4), mp.nstr(res['maxrelQ'],4)))
    print('G7 positive definite (ball LDL^T):', res['G7_pd'])
    for k,v in res.items():
        if k.startswith('floor_'): print('  certified  Q7 - (%s) G7 >= 0 :' % k[6:], v)
    print('\nQ7 (ball, mid +/- rad):')
    for i in range(7):
        print('  ' + ' '.join('%s' % Q7[i][j].str(8, radius=False) for j in range(7)))
