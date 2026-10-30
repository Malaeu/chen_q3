import sympy as s

A0, A1, A2, b1, b2 = s.symbols('A0 A1 A2 b1 b2', real=True)
modes = [-2, -1, 0, 1, 2]
a = {0: A0, 1: A1, 2: A2, -1: A1, -2: A2}
b = {0: s.Integer(0), 1: b1, 2: b2, -1: -b1, -2: -b2}
K = s.Matrix([
    [a[i] if i == j else (b[i] - b[j]) / s.Integer(i - j)
     for j in modes] for i in modes
])
E = s.zeros(5, 3)
E[2, 0] = 1
for n in (1, 2):
    E[2 + n, n] = E[2 - n, n] = 1 / s.sqrt(2)
A = s.simplify(E.T * K * E)
d = [1, s.sqrt(2), s.sqrt(2)]
z = [0, b1, 2 * b2]
for i in range(3):
    for j in range(i + 1, 3):
        assert s.simplify(
            A[i, j] - d[i] * d[j] * (z[i] - z[j]) /
            s.Integer(i * i - j * j)
        ) == 0
c = s.Matrix(s.symbols('c0:3', real=True))
mask = s.diag(-1, -1, 1)
C = sum(A[i, 2] * c[i] * c[2] for i in (0, 1))
assert s.simplify(
    ((mask * c).T * A * (mask * c) - c.T * A * c)[0] + 4 * C
) == 0

# An exactly stationary vector, constructed rationally; no bottom claim.
v = s.Matrix([s.Rational(2), s.Rational(-3), s.Rational(5)])
lam = s.Rational(-2)
B = s.Matrix([
    [0, s.Rational(2, 3), s.Rational(-4, 5)],
    [s.Rational(2, 3), 0, s.Rational(3, 7)],
    [s.Rational(-4, 5), s.Rational(3, 7), 0],
])
for i in range(3):
    B[i, i] = lam - sum(B[i, j] * v[j]
                        for j in range(3) if j != i) / v[i]
t = s.symbols('t0:3', real=True)
y = s.diag(*t) * v
left = (y.T * (B - lam * s.eye(3)) * y)[0]
right = -sum(B[i, j] * v[i] * v[j] * (t[i] - t[j]) ** 2
             for i in range(3) for j in range(i + 1, 3))
assert s.simplify(left - right) == 0

base = s.Matrix([[2, -1], [-1, 2]])
for shift in (0, -5):
    for v, value in (
        (s.Matrix([1, 1]) / s.sqrt(2), 1 + shift),
        (s.Matrix([1, -1]) / s.sqrt(2), 3 + shift),
    ):
        matrix = base + shift * s.eye(2)
        reflected = s.diag(-1, 1) * v
        difference = s.simplify(
            (reflected.T * matrix * reflected)[0] - value
        )
        print(shift, value, difference)
print('Exact structural controls passed; no literal CCM numeric scan.')
