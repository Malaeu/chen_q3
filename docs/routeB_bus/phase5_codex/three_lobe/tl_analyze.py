"""Restrict (C1) to the exact 7-dim kernel, solve the generalized eigenproblem,
split Q on the mean direction z, and run the mandatory 2x2 gluing detector."""
import sys, time, pickle
import mpmath as mp, sympy as sp
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/three_lobe')
from tl_cache import get as build
from tl_kernel import kernel_basis, moment_rows

def to_mp(M):
    return mp.matrix([[mp.mpf(sp.N(M[i,j], mp.mp.dps+10).__str__()) for j in range(M.cols)]
                      for i in range(M.rows)])

def congr(K, M):
    """K^T M K with mpmath matrices."""
    n, m = K.rows, K.cols
    out = mp.matrix(m, m)
    for a in range(m):
        for b in range(m):
            s = mp.mpf(0)
            for i in range(n):
                if K[i,a] == 0: continue
                for j in range(n):
                    if K[j,b] == 0: continue
                    s += K[i,a]*M[i,j]*K[j,b]
            out[a,b] = s
    return out

def gen_eig(Q7, G7):
    """generalized eigenvalues of Q7 v = lam G7 v, G7 SPD, via Cholesky."""
    n = Q7.rows
    L = mp.cholesky(G7)
    Li = mp.inverse(L)
    M = Li*Q7*Li.T
    for i in range(n):                       # symmetrize
        for j in range(i+1, n):
            av = (M[i,j]+M[j,i])/2; M[i,j] = av; M[j,i] = av
    E, V = mp.eigsy(M)
    vecs = [Li.T*V[:, k] for k in range(n)]  # back to kernel coordinates
    return E, vecs, L

def run(dps=50, **kw):
    mp.mp.dps = dps
    r = build(dps=dps, **kw)
    Ks = kernel_basis()
    K  = to_mp(Ks)
    out = {'r': r, 'K': K}
    for name in ('G','Q','Arch','Prime','Pole','D'):
        out[name+'7'] = congr(K, r[name])
    Q7, G7 = out['Q7'], out['G7']
    # Gram positivity in kernel coordinates
    out['G7_chol_ok'] = True
    try:  mp.cholesky(G7)
    except Exception as e: out['G7_chol_ok'] = str(e)
    out['G7_eig'] = mp.eigsy(G7, eigvals_only=True)
    E, V, L = gen_eig(Q7, G7)
    out['lam'] = E; out['vecs'] = V
    # mean direction z = first basis column
    e1 = mp.matrix(7,1); e1[0] = 1
    nrm = (e1.T*G7*e1)[0]
    out['z_split'] = {k: (e1.T*out[k+'7']*e1)[0]/nrm for k in ('Q','Arch','Prime','Pole','D')}
    out['z_G'] = nrm
    return out

def detector():
    """(C16) mandatory detector: A=B=1, E=2 -> S(0) = -3; envelope logic must reject."""
    M = mp.matrix([[1,2],[2,1]])
    A_, B_, E_ = mp.mpf(1), mp.mpf(1), mp.mpf(2)
    S0 = A_ - E_*E_/B_
    v = mp.matrix([[1],[-1]])
    val = (v.T*M*v)[0]
    # envelope logic with a ball radius rad on every entry (Weyl):
    rad = mp.mpf('1e-3')
    lam = mp.eigsy(M, eigvals_only=True)
    return dict(S0=S0, witness_value=val, eig=lam,
                upper_lambda_min=lam[0] + 2*rad, rejected=bool(lam[0] + 2*rad < 0))

if __name__ == '__main__':
    t0 = time.time()
    o = run()
    mp.mp.dps = 25
    print('runtime build %.1fs' % o['r']['runtime'])
    print('\nG7 eigenvalues:'); [print('  ', mp.nstr(x, 12)) for x in o['G7_eig']]
    print('G7 Cholesky ok:', o['G7_chol_ok'])
    print('\ngeneralized eigenvalues lam(Q7,G7):')
    for x in o['lam']: print('  ', mp.nstr(x, 20))
    print('\nQ on z (normalized by G):')
    for k,v in o['z_split'].items(): print('   %-6s %s' % (k, mp.nstr(v, 20)))
    print('   check (C7): log(4/3)/6 =', mp.nstr(mp.log(mp.mpf(4)/3)/6, 20))
    print('\n2x2 detector:', {k: (mp.nstr(v,10) if isinstance(v,mp.mpf) else v)
                              for k,v in detector().items() if k!='eig'})
    with open('/home/chirurgie/.claude/jobs/4b35770d/tmp/three_lobe/analysis.pkl','wb') as f:
        pickle.dump({'lam':[mp.nstr(x,40) for x in o['lam']],
                     'z':{k:mp.nstr(v,40) for k,v in o['z_split'].items()}}, f)
    print('\nTOTAL %.1fs' % (time.time()-t0))
