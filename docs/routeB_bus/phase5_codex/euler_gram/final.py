"""Final tables: convergence of the k_2 lower bound + margin sandwich."""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import k2, margin

D = os.path.dirname(os.path.abspath(__file__))
Z = np.load(os.path.join(D, '..', 'mellin_d2', 'd_two.npz'))

def load(p):
    return np.load(p)

def conv(paths, pts=(16., 40., 120., 200., 300., 400., 500., 600.)):
    print("--- convergence of the k_2 LOWER bound (Galerkin, monotone in the trial span)")
    print("run   nodes rank  range        U     h    over  " + "  ".join(f"{x:8.1f}" for x in pts))
    base = None
    for tag, p in paths:
        A = load(p)
        v = np.array([A['k2_lo'][int(round(x/0.25))] for x in pts])
        print(f"{tag:4s} {A['nodes'].size:6d} {A['rank']:5d} [{A['lo']:.0f},{A['hi']:.0f}]"
              f" {A['U']:6.0f} {A['h']:.3f} {A['over']:.1f}  " + "  ".join(f"{y:.6f}" for y in v))
        if base is None: base = v
    print("spread over the runs:                                 " +
          "  ".join(f"{d:.2e}" for d in
                    (np.max([np.array([load(p)['k2_lo'][int(round(x/0.25))] for x in pts]) for _, p in paths], axis=0) -
                     np.min([np.array([load(p)['k2_lo'][int(round(x/0.25))] for x in pts]) for _, p in paths], axis=0))))

def margins(path, ref=None):
    A = load(path); xi = A['xi']; lo = A['k2_lo']; b2 = A['b2']
    z2 = A['z2'] if 'z2' in A.files else None
    q2 = k2.q_two(xi)
    d_lo = lo - q2/(2*np.pi)
    ell2 = np.interp(xi, Z['xi'], Z['lead'])
    dJ8 = np.interp(xi, Z['xi'], Z['d_J8'])
    print("\n--- margins.  m(v) = (1/2pi) int W q_2 - int W k_2 ;  k_2 >= k_2^lo  =>  m <= m_UP")
    print("  T  chan   1-mass    (1/2pi)intWq2   intW k2_lo    m_UP        m(J8 table)   floor/Qsc   m_UP - Qsc")
    out = {}
    for T in (60., 120., 240., 340.):
        H = margin.Hnorm(T)
        for sg, nm in ((-1, 'minus'), (+1, 'plus')):
            W = margin.weight(xi, T, sg, H)
            defc = 1 - np.trapezoid(W, xi)/(2*np.pi)
            qp = np.trapezoid(W*q2, xi)/(2*np.pi)
            kl = np.trapezoid(W*lo, xi)
            mup = qp - kl
            F = -np.trapezoid(W*ell2, xi)
            m8 = -np.trapezoid(W*dJ8, xi)
            band = None
            if z2 is not None:
                hi = b2*(A['E'] + np.maximum(z2, 0.0)/k2.G0)
                band = qp - np.trapezoid(W*hi, xi)
            out[(T, nm)] = (mup, band, F, m8)
            print(f"{T:5.0f} {nm:5s} {defc:9.2e}  {qp:+.6f}   {kl:+.6f}   {mup:+.6f}"
                  f"   {m8:+.6f}   {F:+.6f}   {mup-F:+.6f}"
                  + (f"   [resid-band low {band:+.5f}]" if band is not None else ""))
    return out

if __name__ == '__main__':
    base = '/home/chirurgie/.claude/jobs/4b35770d/tmp/euler_gram/'
    conv([('A', base+'k2_A.npz'), ('B', base+'k2_B.npz'), ('C', base+'k2_C.npz'), ('D', base+'k2_D.npz')])
    margins(base+'k2_D.npz')
    margins(base+'k2_B.npz')
