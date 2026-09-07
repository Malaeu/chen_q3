"""Extra structural checks on a prod2 output."""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import k2

def run(path):
    A = np.load(path); xi = A['xi']; lo = A['k2_lo']; kinf = A['kinf']; b2 = A['b2']
    hi = A['k2_hi']
    print("(19) sandwich  |b|^2 k_inf/g1 <= k_2 <= |b|^2 k_inf/g0 :",
          bool(np.all(lo >= b2*kinf/k2.G1 - 1e-9)), bool(np.all(hi <= b2*kinf/k2.G0 + 1e-9)))
    per = 2*np.pi/np.log(2); a = np.log(2.0); r = 2**-0.5
    print(f"first cosine coefficient of k_2 - k_inf over whole periods (target -a r/pi = {-a*r/np.pi:.6f}):")
    for x0, x1 in [(50, 294.8), (50, 593.9), (100, 299.4), (100, 598.6), (200, 598.9), (100, 698.0)]:
        n = int((x1-x0)/per); xb = x0 + n*per
        s = (xi >= x0) & (xi <= xb)
        L = xb - x0
        c1 = 2*np.trapezoid((lo[s]-kinf[s])*np.cos(a*xi[s]), xi[s])/L
        c1h = 2*np.trapezoid((hi[s]-kinf[s])*np.cos(a*xi[s]), xi[s])/L
        s1 = 2*np.trapezoid((lo[s]-kinf[s])*np.sin(a*xi[s]), xi[s])/L
        print(f"   [{x0},{xb:.3f}] {n:3d} periods:  c1 = {c1:+.6f} .. {c1h:+.6f}   s1 = {s1:+.2e}")
    m = (xi >= 16)
    print(f"k_2 > 0 everywhere on the grid: {bool(np.all(lo > -1e-12))};  min lo = {lo.min():.3e}")

if __name__ == '__main__':
    for p in sys.argv[1:]:
        run(p)
