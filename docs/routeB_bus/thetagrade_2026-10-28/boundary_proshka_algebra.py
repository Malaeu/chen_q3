#!/usr/bin/env python3
"""Exact algebra controls for BOUNDARY; no literal CCM numerical scan."""
from pathlib import Path
from itertools import product
import hashlib
import sympy as s


def laplacian(n, edges):
    M = s.zeros(n)
    for i, j, w in edges:
        b = s.zeros(n, 1)
        b[i], b[j] = 1, -1
        M += w * b * b.T
    return M


def quad(M, v):
    return s.simplify((v.T * M * v)[0])


def main():
    request = Path('/mnt/data/PROSHKA_REQUEST_BOUNDARY_2026-10-30.txt')
    if request.exists():
        raw = request.read_bytes()
        assert len(raw) == 6891 and raw.count(b'\n') == 108
        assert hashlib.sha256(raw).hexdigest() == '50bfc8c63d663bae15b916936646eadf8379c9a78dedbf3d934d58db8bc727ba'
        print('request: exact byte/hash check PASS')

    L3 = laplacian(3, [(0, 1, s.S.One), (1, 2, s.S.One),
                         (0, 2, -s.Rational(3, 4))])
    for bits in product([0, 1], repeat=3):
        assert quad(L3, s.Matrix(bits)) >= 0
    a3 = s.Matrix([1, s.Rational(1, 2), 0])
    assert quad(L3, a3) == -s.Rational(1, 4)
    assert s.simplify(3 * quad(L3, a3) / (a3.dot(a3))) == -s.Rational(3, 5)
    print('triangle: all cuts PASS; voltage=-1/4; normalized gain=-3/5')

    Lp = laplacian(4, [(0, 1, s.S.One), (1, 2, s.S.One), (2, 3, s.S.One)])
    B = s.Matrix([[1, 0], [0, 1], [-1, 0], [0, -1]])
    R = s.simplify(B.T * Lp.pinv() * B)
    assert R == s.Matrix([[2, 1], [1, 2]])
    load = s.Rational(2, 5) * R
    assert set(load.eigenvals()) == {s.Rational(6, 5), s.Rational(2, 5)}
    L4 = Lp - s.Rational(2, 5) * B * B.T
    assert quad(L4, s.Matrix([3, 2, 1, 0])) == -s.Rational(1, 5)
    print('four-path: single loads=4/5; joint top load=6/5; voltage=-1/5')

    # For a fixed degree d, the plant has m=d+2 (m+1 nodes).
    # d_i match the orthonormal even-basis weights; the matrix is NOT CCM.
    for degree in [1, 2, 3, 4]:
        n = degree + 3
        x = [s.Integer(i * i) for i in range(n)]
        d = [s.S.One] + [s.sqrt(2)] * (n - 1)
        v = s.Matrix(d)
        X = s.diag(*x)
        u = X**2 * v
        A = (X*v)*v.T + v*(X*v).T
        assert X*A - A*X == u*v.T - v*u.T
        c = s.Matrix([1/(d[i]*s.prod(x[i]-x[j] for j in range(n) if j != i))
                      for i in range(n)])
        for k in range(degree + 2):
            assert s.simplify((v.T*X**k*c)[0]) == 0
        for k in range(degree + 1):
            assert s.simplify(A*X**k*c) == s.zeros(n, 1)
        y = s.zeros(n, 1)
        y[0], y[1] = 2*s.sqrt(2), -1
        assert quad(A, y) == -4 and y.dot(y) == 9
        if degree >= 2:
            S0 = (v.T*c)[0]
            Sx = (v.T*X*c)[0]
            SF = (u.T*c)[0]
            SFx = (u.T*X*c)[0]
            assert all(s.simplify(z) == 0 for z in (S0, Sx, SF, SFx))
        print(f'polynomial plant d={degree}: exact stationary invisibility PASS; Rayleigh(y)=-4/9')

    n = 4
    x = [s.Integer(i*i) for i in range(n)]
    d = [s.S.One] + [s.sqrt(2)]*(n-1)
    F = list(map(s.Rational, [0, 3, -2, 5]))
    c = s.Matrix([s.Rational(z)/d[i] for i, z in enumerate([1, -2, 3, -4])])
    A = s.zeros(n)
    for i in range(n):
        for j in range(n):
            if i != j:
                A[i, j] = d[i]*d[j]*(F[i]-F[j])/(x[i]-x[j])
    lam = s.Rational(2, 7)
    for i in range(n):
        A[i, i] = lam-sum(A[i,j]*c[j] for j in range(n) if j != i)/c[i]
    X = s.diag(*x)
    v = s.Matrix(d)
    u = s.Matrix([d[i]*F[i] for i in range(n)])
    assert s.simplify(A*c-lam*c) == s.zeros(n, 1)
    assert s.simplify(X*A-A*X-u*v.T+v*u.T) == s.zeros(n)
    S0, SF = (v.T*c)[0], (u.T*c)[0]
    Sx, SFx = (v.T*X*c)[0], (u.T*X*c)[0]
    assert s.simplify(quad(A-lam*s.eye(n), X*c)-(Sx*SF-S0*SFx)) == 0
    a = s.Matrix([1, s.Rational(-1, 2), s.Rational(2, 3), 0])
    D = s.diag(*a)
    wenergy = -sum(A[i,j]*c[i]*c[j]*(a[i]-a[j])**2
                   for i in range(n) for j in range(i+1,n))
    assert s.simplify(quad(A-lam*s.eye(n), D*c)-wenergy) == 0
    z = s.symbols('z0:'+str(n))
    Wpair = -sum(d[i]*d[j]*c[i]*c[j]*(x[i]-x[j])*(i*z[i]-j*z[j])
                 for i in range(n) for j in range(i+1,n))
    Wmoment = Sx*sum(d[i]*c[i]*i*z[i] for i in range(n)) \
              -S0*sum(d[i]*c[i]*i**3*z[i] for i in range(n))
    assert s.simplify(Wpair-Wmoment) == 0
    print('displacement, eigenrelation, multiplier energy, sine coefficients: PASS')

    t = s.symbols('t', real=True)
    for degree in [1, 2]:
        edge = s.cos(s.pi*t)**(4*degree)
        for k in range(4*degree):
            assert s.simplify(s.diff(edge,t,k).subs(t,s.Rational(1,2))) == 0
            assert s.simplify(s.diff(edge,t,k).subs(t,-s.Rational(1,2))) == 0
        zvar = s.symbols('z')
        laurent = s.expand(((zvar+2+zvar**-1)/4)**(2*degree))
        assert s.Poly(s.expand(zvar**(2*degree)*laurent),zvar).degree() == 4*degree
    print('flat endpoint factor: exact endpoint jets and degree: PASS')

    # Strict prime-discrepancy majorization is not necessary for negative signed energy.
    W = -s.sin(2*s.pi*t)
    Rtoy = 100*s.cos(4*s.pi*t)
    assert s.integrate(Rtoy*s.diff(W,t),(t,0,1)) == 0
    assert s.integrate((1-t)*W,(t,0,1)) == -1/(2*s.pi)
    print('majorant countercontrol: signed error=0, negative reference=-1/(2*pi): PASS')
    print('ALL EXACT CONTROLS PASS; no literal CCM eigenvalue claim.')

if __name__ == '__main__':
    main()
