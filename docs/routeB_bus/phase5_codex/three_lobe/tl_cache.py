"""Build once, cache to disk (mpmath matrices as decimal strings)."""
import os, pickle, sys
import mpmath as mp
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/three_lobe')
CACHE = '/home/chirurgie/.claude/jobs/4b35770d/tmp/three_lobe/build_%s.pkl'

def _dump(M): return [[mp.nstr(M[i,j], mp.mp.dps+5) for j in range(M.cols)] for i in range(M.rows)]
def _load(L): return mp.matrix([[mp.mpf(x) for x in row] for row in L])

def get(dps=50, **kw):
    tag = 'dps%d_%s' % (dps, '_'.join('%s%s'%(k,v) for k,v in sorted(kw.items())))
    path = CACHE % tag
    if os.path.exists(path):
        mp.mp.dps = dps
        d = pickle.load(open(path,'rb'))
        r = {k: _load(v) for k,v in d['mats'].items()}
        r['m_eta'] = mp.mpf(d['m_eta']); r['runtime'] = d['runtime']
        r['active'] = [(n, mp.mpf(w)) for n,w in d['active']]
        r['scanned'] = d['scanned']
        r['Mmom'] = [[mp.mpf(x) for x in row] for row in d['Mmom']]
        from tl_core import packet
        r['P'] = packet(dps)
        return r
    from tl_build import build
    r = build(dps=dps, **kw)
    mp.mp.dps = dps
    pickle.dump(dict(mats={k: _dump(r[k]) for k in ('g','G','D','Arch','Prime','Pole','Q','D0')},
                     m_eta=mp.nstr(r['m_eta'], dps+5), runtime=r['runtime'],
                     active=[(n, mp.nstr(w, dps+5)) for n,w in r['active']],
                     scanned=r['scanned'],
                     Mmom=[[mp.nstr(x, dps+5) for x in row] for row in r['Mmom']]),
                open(path,'wb'))
    return r
