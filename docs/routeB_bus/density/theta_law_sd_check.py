#!/usr/bin/env python3
"""Observer check (2026-09-12, rule 13): three identities behind ADVICE DENSITYSD.

Objects (DENSITY verdict 2026-09-11, DN2/DN11/DN12):
  Z  = sum_{n>=2} Gamma(2,1)/(pi (n^2-1)),  L_Z(z) = prod_{n>=2} (1+z/(pi(n^2-1)))^{-2}
  T  = shifted-rate law of DN2,            L_T(z) = 4 pi^2 L_Z(z+pi)/(z+pi)^2
Claims checked (stdlib only; products truncated at N, error ~ 2z/(pi N)):
  (I1) L_T(z) = prod_{n>=1}(1+z/(pi n^2))^{-2} = (sqrt(pi z)/sinh sqrt(pi z))^2   => T = (pi/2) S_2 (Pitman-Yor 2003)
  (I2) BDLP cumulant: kappa_L(z) = z kappa_T'(z) = -2 sum_n z/(pi n^2+z)  = int_0^inf (e^{-zx}-1)(-theta'(x)) dx,
       theta(x)=sum_{n in Z} e^{-pi n^2 x};  i.e. the background driving Levy process of T has Levy density -theta'(x) on x>0
  (I3) half-thinning DN11/DN12 at rho=1/2:  log L_T(z) - log L_T(z/2) = int_0^{log 2} kappa_L(e^{-u} z) du
       i.e. Y_{1/2} is the OU-type increment over time log 2 driven by L.
DIAGNOSTIC_NEVER_A_PROOF: numbers expose a mismatch; the analytic proofs are three lines each (see ADVICE).
"""
import math
N = 200000
def L_T_prod(z): return math.exp(-2*sum(math.log(1+z/(math.pi*n*n)) for n in range(1, N+1)))
def L_T_closed(z): s = math.sqrt(math.pi*z); return (s/math.sinh(s))**2
def L_Z_prod(z): return math.exp(-2*sum(math.log(1+z/(math.pi*(n*n-1))) for n in range(2, N+1)))
def kappa_T(z): s = math.sqrt(math.pi*z); return 2*math.log(s/math.sinh(s))
def kappa_L_series(z, M=100000): return -2*sum(z/(math.pi*n*n+z) for n in range(1, M+1))
def kappa_L_levy(z, M=100000): return sum(2*(math.pi*n*n/(math.pi*n*n+z)-1) for n in range(1, M+1))

print("I1  L_T product vs closed form (rel diff should equal truncation bound 2z/(pi N))")
for z in (0.3, 1.0, 5.0):
    p, c = L_T_prod(z), L_T_closed(z)
    print(f"    z={z:4}: prod={p:.10e} closed={c:.10e} rel={abs(p-c)/c:.1e} bound={2*z/(math.pi*N):.1e}")
z = 1.0
print(f"DN2 4pi^2 L_Z(z+pi)/(z+pi)^2 = {4*math.pi**2*L_Z_prod(z+math.pi)/(z+math.pi)**2:.8e}  vs closed {L_T_closed(z):.8e}")
z, h = 2.0, 1e-6
print(f"I2  z*kappa_T'(z)={z*(kappa_T(z+h)-kappa_T(z-h))/(2*h):.8f}  series={kappa_L_series(z):.10f}  Levy(-theta')={kappa_L_levy(z):.10f}")
print("I3  half-thinning = OU increment over log 2")
for z in (1.0, 3.0, 10.0):
    lhs = math.log(L_T_closed(z)/L_T_closed(z/2)); M = 400; hh = math.log(2)/M
    rhs = sum((kappa_L_series(math.exp(-i*hh)*z, 20000)+kappa_L_series(math.exp(-(i+1)*hh)*z, 20000))/2*hh for i in range(M))
    print(f"    z={z:4}: lhs={lhs:.8f} rhs={rhs:.8f} diff={lhs-rhs:.1e}")
