"""Validation + margin tables from a prod2 output."""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import k2, margin

def run(path, zfloor=None):
    A = np.load(path)
    xi = A['xi']; lo = A['k2_lo']; kinf = A['kinf']; b2 = A['b2']; z2 = A['z2']
    if zfloor is None:
        zfloor = max(0.0, -float(z2.min()))
    hi = b2*(A['E'] + np.maximum(z2 + zfloor, 0.0)/k2.G0)
    q2 = k2.q_two(xi)
    d_lo = lo - q2/(2*np.pi); d_hi = hi - q2/(2*np.pi)
    Z = np.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'mellin_d2', 'd_two.npz'))
    dJ = {J: np.interp(xi, Z['xi'], Z['d_J'+str(J)]) for J in (6, 7, 8)}
    ell2 = np.interp(xi, Z['xi'], Z['lead'])
    print(f"=== {os.path.basename(path)}  nodes={A['nodes'].size} rank={A['rank']} "
          f"U={A['U']} h={A['h']} over={A['over']} range=[{A['lo']},{A['hi']}]")
    print(f"    gram_err(diag of quadrature truncation) = {A['gram_err']:.2e}")
    print(f"    z2: min={z2.min():.2e} median={np.median(z2):.2e} max={z2.max():.2e}; floor used {zfloor:.2e}")
    print(f"    k_2 sandwich width  median={np.median(hi-lo):.2e}  max={np.max(hi-lo):.2e}")
    print(f"    min k_2 lower bound = {lo.min():.3e} at xi={xi[lo.argmin()]}  (k_2>=0 required)")
    print(f"    1-comp/kinf max on [16,600] = {np.nanmax((1-A['comp']/np.maximum(kinf,1e-30))[(xi>=16)&(xi<=600)]):.2e}")
    m = (xi >= 16) & (xi <= 600)
    print(f"    d_2: mean(J8 - lo)={np.mean((dJ[8]-d_lo)[m]):+.3e}  rms={np.sqrt(np.mean((dJ[8]-d_lo)[m]**2)):.3e}"
          f"  frac J8 inside [lo,hi] = {np.mean(((dJ[8]>=d_lo)&(dJ[8]<=d_hi))[m]):.3f}")
    per = 2*np.pi/np.log(2)
    dist = np.abs(((xi/per+0.5) % 1)-0.5)*per
    for a_, b_ in [(0, 1), (1, 2), (2, 3), (3, 4.6)]:
        s = m & (dist >= a_) & (dist < b_)
        print(f"      |xi - 2 pi k/log2| in [{a_},{b_}): mean(J8-lo)={np.mean((dJ[8]-d_lo)[s]):+.3e} "
              f"rms={np.sqrt(np.mean((dJ[8]-d_lo)[s]**2)):.3e}  (sandwich width {np.mean((d_hi-d_lo)[s]):.3e})")
    for X in (100, 200, 400, 600, 700):
        s = xi <= X
        print(f"    int_0^{X} d_2 = {np.trapezoid(d_lo[s],xi[s]):+.5f} .. {np.trapezoid(d_hi[s],xi[s]):+.5f}"
              f"   (d_inf: {np.trapezoid(np.interp(xi[s],Z['xi'],Z['dinf']),xi[s]):+.5f})")
    print()
    print("  T   chan   mass    (1/2pi)int W q2   int W k2 [lo,hi]        m = [lower, upper]      floor/Qsc     m-Qsc")
    rows = []
    for T in (60., 120., 240., 340.):
        H = margin.Hnorm(T)
        for sg, nm in ((-1, 'minus'), (+1, 'plus')):
            W = margin.weight(xi, T, sg, H)
            mass = np.trapezoid(W, xi)/(2*np.pi)
            qp = np.trapezoid(W*q2, xi)/(2*np.pi)
            klo = np.trapezoid(W*lo, xi); khi = np.trapezoid(W*hi, xi)
            mup = qp - klo; mlo = qp - khi
            F = -np.trapezoid(W*ell2, xi)
            m8 = -np.trapezoid(W*dJ[8], xi)
            print(f"{T:5.0f} {nm:5s} {mass:.5f}  {qp:+.6f}   [{klo:+.6f},{khi:+.6f}]  "
                  f"[{mlo:+.6f},{mup:+.6f}]  {F:+.6f}  [{mlo-F:+.6f},{mup-F:+.6f}]   (J8: {m8:+.6f})")
            rows.append((T, nm, mass, qp, klo, khi, mlo, mup, F, m8))
    return rows

if __name__ == '__main__':
    for p in sys.argv[1:]:
        run(p)
