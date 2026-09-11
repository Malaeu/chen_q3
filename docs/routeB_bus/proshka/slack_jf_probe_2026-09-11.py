from mpmath import mp, mpf, exp, pi, diff, nsum, inf
mp.dps = 40
def Phi(x):
    x = mpf(x)
    return exp(x/2)*nsum(lambda n: (4*pi**2*n**4*exp(4*x) - 6*pi*n**2*exp(2*x))*exp(-pi*n**2*exp(2*x)), [1, inf])
def J(x):
    x = mpf(x)
    f0, f1, f2 = Phi(x), diff(Phi, x, 1), diff(Phi, x, 2)
    return x*(f1**2 - f0*f2) + f0*f1
xs = [mpf(s) for s in "0.001 0.01 0.05 0.1 0.2 0.3 0.5 0.7 1 1.5 2 2.5 3 4".split()]
neg = 0
for x in xs:
    j = J(x); f0 = Phi(x)
    print(f"x={x!s:>6}  J_f/f^2={mp.nstr(j/f0**2, 12):>20}  f={mp.nstr(f0,8)}")
    neg += (j < 0)
print("negative points:", neg, "of", len(xs))
