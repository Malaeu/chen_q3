"""Final ledger and interval [L_F, U_F], SCALARFLOOR (38)."""
import re, sys
from flint import arb, ctx
import budget

PREC = 400
ctx.prec = PREC


def read_ball(path, key):
    txt = open(path).read()
    m = re.search(re.escape(key) + r"\s*=\s*\[?([-+0-9.eE]+)\s*\+/-\s*([0-9.eE+-]+)\]?", txt)
    if m is None:                       # exact ball printed without a radius
        m = re.search(re.escape(key) + r"\s*=\s*([-+0-9.eE]+)", txt)
        mid, rad = m.group(1), "0"
    else:
        mid, rad = m.group(1), m.group(2)
    mid = float(mid); rad = float(rad)
    return arb(mid, rad * 1.0001 + abs(mid) * 2.0 ** -48 + 1e-300)


def main(path, X, J0):
    Ic = read_ball(path, "I_compact")
    Eq = read_ball(path, "E_quad")
    ctx.prec = PREC
    eps = budget.eps_J(J0)
    T = budget.Tstar()
    mu = budget.mu_X(X)
    e_euler = 4 * arb.pi() * eps
    e_freq = 2 * T * mu
    L = Ic.mid() - Ic.rad() - Eq.abs_upper() - e_euler.abs_upper() - e_freq.abs_upper()
    U = Ic.mid() + Ic.rad() + Eq.abs_upper() + e_euler.abs_upper() + e_freq.abs_upper()
    print("compact  I  = ", Ic.str(20))
    print("E_quad      <=", Eq.abs_upper().str(10))
    print("4 pi eps_J  <=", e_euler.abs_upper().str(10), f"  (J0={J0}, eps={eps.str(8)})")
    print("2 Tstar mu_X<=", e_freq.abs_upper().str(10), f"  (X={X}, Tstar={T.str(10)}, mu={mu.str(8)})")
    print("L_F =", L.str(20))
    print("U_F =", U.str(20))
    print("1/500 =", (arb(1) / 500).str(20))
    print("L_F >= 1/500 :", bool(L > arb(1) / 500))


if __name__ == '__main__':
    main(sys.argv[1], float(sys.argv[2]), int(sys.argv[3]))
