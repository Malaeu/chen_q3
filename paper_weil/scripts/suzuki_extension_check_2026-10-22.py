# (3.2): P_t(z) = sum_gamma m (e^{-i gamma t} - 1) / (gamma (z - gamma)),  t >= 0
# (A) letter:  P_{-tau}(z) := P_tau(-z)
# (B) Suzuki:  P_{-tau}(z) := conj(P_tau(conj z))
# (C) "(3.2) for all real t": plug t = -tau directly
import cmath
base = [14.134725+0.3j, 21.022040-0.7j, 25.010858+1.1j]          # fake zeros off the line
G = set()
for g in base:
    for s in (g, -g, g.conjugate(), -g.conjugate()):              # symmetric under gamma->-gamma and gamma->conj
        G.add(s)
G = sorted(G, key=lambda w: (w.real, w.imag))
def P(t, z): return sum((cmath.exp(-1j*g*t)-1)/(g*(z-g)) for g in G)
for tau, z in [(0.7, 3.0+0.4j), (2.3, -1.5+2.0j), (0.05, 0.2-0.9j)]:
    A = P(tau, -z); B = P(tau, z.conjugate()).conjugate(); C = P(-tau, z)
    print(f"tau={tau} z={z}: |A-B|={abs(A-B):.2e} |A-C|={abs(A-C):.2e} |B-C|={abs(B-C):.2e}  (A={A:.6f})")
# control: break the conj-symmetry -> A and B must diverge
G = [g for g in G if g.imag >= 0] + [-g for g in G if g.imag >= 0]
G = sorted(set(G), key=lambda w:(w.real,w.imag))
tau, z = 0.7, 3.0+0.4j
A = P(tau, -z); B = P(tau, z.conjugate()).conjugate(); C = P(-tau, z)
print(f"control (only gamma->-gamma symmetry): |A-B|={abs(A-B):.2e} |A-C|={abs(A-C):.2e}")
