"""PINGEOM limit: threshold a* as the minimum of the autocorrelation of h' (h = MARKOV (4.3) theta radical vector).
Route 1 (x-space): R(a) = int h'(x) h'(x+a) dx, a* = root of R'(a) = int h'(x) h''(x+a) dx.
Route 2 (Riemann Xi): h-hat(t) = 4 Xi(t), Xi(t) = xi(1/2 + i t) real, so R(a) = (8/pi) int_0^inf t^2 Xi(t)^2 cos(t a) dt and
R'(a) = -(8/pi) int_0^inf t^3 Xi(t)^2 sin(t a) dt. DIAGNOSTIC_NEVER_A_PROOF.
"""
import mpmath as mp
mp.mp.dps = 30
def h(x):
    x = abs(x); s = mp.mpf(0); n = 1
    while True:
        e2 = mp.e**(2 * x) * n * n
        if mp.pi * e2 > 120: break
        s += (16 * mp.pi**2 * e2**2 - 24 * mp.pi * e2) * mp.e**(-mp.pi * e2); n += 1
    return mp.e**(x / 2) * s
hp = lambda x: mp.diff(h, x); hpp = lambda x: mp.diff(h, x, 2)
R1d = lambda a: mp.quad(lambda x: hp(x) * hpp(x + a), [-3, -1, 0, 1, 3])
a1 = mp.findroot(R1d, 0.575)
Xi = lambda t: mp.re(0.5 * (0.5 + 1j * t) * (-0.5 + 1j * t) * mp.pi**(-(0.5 + 1j * t) / 2) * mp.gamma((0.5 + 1j * t) / 2) * mp.zeta(0.5 + 1j * t))
pts = [0, 5, 10, 14.13, 20, 30, 45, 60, 80]
R2d = lambda a: -(8 / mp.pi) * mp.quad(lambda t: t**3 * Xi(t)**2 * mp.sin(t * a), pts)
a2 = mp.findroot(R2d, 0.575)
R2 = lambda a: (8 / mp.pi) * mp.quad(lambda t: t**2 * Xi(t)**2 * mp.cos(t * a), pts)
print("a* (x-space)   =", mp.nstr(a1, 12))
print("a* (Riemann Xi) =", mp.nstr(a2, 12))
print("R(0) =", mp.nstr(R2(0), 8), " R(a*) =", mp.nstr(R2(a2), 8), " R(0.3) =", mp.nstr(R2(0.3), 8), " R(1.0) =", mp.nstr(R2(1.0), 8))
print("x-space check R(0) =", mp.nstr(mp.quad(lambda x: hp(x)**2, [-3, -1, 0, 1, 3]), 8))
