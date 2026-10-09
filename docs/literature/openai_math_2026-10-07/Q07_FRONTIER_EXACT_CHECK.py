"""Exact algebra checks for source Q7; not verification of its analytic premises.

Run from repository root: venv_djo/bin/python docs/literature/
openai_math_2026-10-07/Q07_FRONTIER_EXACT_CHECK.py
Requires the existing SymPy environment. No floating-point assertions.
"""
import sympy as s

l, b, d, x, k = s.symbols("l b d x k")
alpha = s.Rational(5, 6)
B = 2 - 2*x/(3*k)
D = 3 - x - 2*x/(3*k)
P = B*(1-x)
J = (alpha-d)*D + d*P
R = 1-d + (alpha-d)*d*P/(2*J)
E = (3*R*b + 9*R*l + 3*R - 2*b
     - 6*(s.Rational(11, 12)-l/4) + 6*d*l*x + 6*d*l + 3*d - 3*l + 1)/6
N = (3024*l+720)*d**2 + (5760*l-1908)*d + 2035-11100*l
assert s.cancel(E.subs({k:s.Rational(3,4), b:s.Rational(1,8), x:s.Rational(1,2)})
                + N/(48*(185-138*d))) == 0
assert s.expand(s.discriminant(N,d)-144*(1162800*l*l-101580*l-15419)) == 0

u,v = s.symbols("u v")
pol = s.cancel((-12*J*E).subs({k:s.Rational(3,4), l:s.Rational(167,1000), b:s.Rational(1,8)}))
minima = []
for da,db in [(0,s.Rational(1,6)), (s.Rational(1,6),s.Rational(1,3))]:
    for xa,xb in [(0,s.Rational(1,4)), (s.Rational(1,4),s.Rational(1,2))]:
        p = s.Poly(pol.subs({d:da+(db-da)*u, x:xa+(xb-xa)*v}),u,v)
        assert p.degree(u) <= 2 and p.degree(v) <= 3
        coefs = [sum(p.coeff_monomial(u**i*v**j)*s.binomial(r,i)/s.binomial(2,i)
                     *s.binomial(t,j)/s.binomial(3,j)
                     for i in range(r+1) for j in range(t+1))
                 for r in range(3) for t in range(4)]
        minima.append(min(coefs))
assert minima == list(map(s.Rational, ["15373/108000", "1201/9000", "21643/864000", "19/4000"]))
print("Bernstein minima:", minima)

Nt = (-432*l*l+468*l+138)*d*d + (-720*l*l+1338*l-361)*d + 1500*l*l-2375*l+385
assert s.cancel(E.subs({k:alpha-l/2, b:s.Rational(1,8), x:s.Rational(1,2)})
                + Nt/(48*(35-25*l-(26-18*l)*d))) == 0
Q = 3110400*l**4-8838720*l**3+6593364*l*l-375756*l-82199
assert s.expand(s.discriminant(Nt,d)-Q) == 0
cubic = 657*l**3-954*l*l+21*l+20
for f,lo,hi in [(Q,"0.16683806526449","0.16683806526450"),
                (cubic,"0.16683858898627","0.16683858898628")]:
    lo,hi = map(s.Rational,(lo,hi))
    assert f.subs(l,lo)*f.subs(l,hi) < 0
    assert s.Poly(f,l).count_roots(lo,hi) == 1
    assert s.Poly(f,l).count_roots(s.Rational(1,6),s.Rational(167,1000)) == 1
    print("Unique root in full check interval; isolated in",lo,hi)
assert s.cancel(E.subs({k:s.Rational(3,4), l:s.Rational(2503,15000), b:s.Rational(1,8),
                       d:s.Rational(29,75), x:s.Rational(1,2)})) == s.Rational(189481,4936500000)
print("PASS: identities, exact certificates, isolation, failed-iteration control.")
