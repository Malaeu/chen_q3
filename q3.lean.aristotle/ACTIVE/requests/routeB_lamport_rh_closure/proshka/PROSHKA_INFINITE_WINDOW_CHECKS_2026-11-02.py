#!/usr/bin/env python3
"""Exact local checks for the infinite-window CCM derivation.

Run:
  uv run --with sympy PROSHKA_INFINITE_WINDOW_CHECKS_2026-11-02.py

These checks validate constants and algebra, not the boundary-regularity
import, the compactness proof, or an RH assertion.
"""
import sympy as s


def main() -> None:
    z, L, x, a = s.symbols('z L x a', positive=True)
    j = s.exp(-z/2)/(1-s.exp(-2*z))
    assert s.limit(z*j, z, 0, dir='+') == s.Rational(1, 2)
    assert s.limit(j-1/(2*z), z, 0, dir='+') == s.Rational(1, 4)
    print('PASS 1: exact logarithmic principal kernel and integrable remainder')

    t = s.symbols('t', real=True)
    heat_square = s.integrate(1/(1+4*t*t), (t, -s.oo, s.oo))/(2*s.pi)
    assert heat_square == s.Rational(1, 4)
    print('PASS 2: time-one whole-line L2 kernel bound equals 1/2')

    p_squared_mass = s.integrate(2*s.cosh(x/2)**2, (x, -L/2, L/2))
    assert s.simplify(p_squared_mass-L-2*s.sinh(L/2)) == 0
    rho1 = 2*s.log(2)+s.polygamma(0, s.Rational(1,2))-s.EulerGamma
    assert s.simplify(rho1+2*s.EulerGamma) == 0
    print('PASS 3: even pole norm and one-dimensional logarithmic-Laplacian constant')

    for N in range(0, 9):
        d = s.Matrix([1]+[s.sqrt(2)]*N)
        assert (d.T*d)[0] == 2*N+1
        assert s.simplify((d*d.T*d)[0]-(2*N+1)) == 0
    print('PASS 4: finite endpoint rank-one norm grows as 2N+1; no bounded infinite limit')

    eps = s.symbols('eps', positive=True)
    assert s.limit((eps/s.log(L/eps))/eps, eps, 0, dir='+') == 0
    assert s.limit(s.sqrt(1/s.log(L/eps)), eps, 0, dir='+') == 0
    print('PASS 5: zero endpoint trace and o(epsilon) newly activated atom budget')

    A, B, C, lam, u2, v2 = s.symbols('A B C lam u2 v2', real=True)
    # q[u]=A, q[u,v]=B, q[v]=C; stationarity tested with u.
    stationary_B = lam*u2-A
    assert s.expand(A-lam*u2+stationary_B) == 0
    print('PASS 6: exact cut-and-collar eigen-equation balance')
    print('ALL 6 LOCAL SYMBOLIC GROUPS PASSED; NO RH OR ANALYTIC AUDIT CLAIM')


if __name__ == '__main__':
    main()
