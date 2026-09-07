"""Exact algebraic 7-dimensional kernel of the two total-moment rows, and the
restricted generalized eigenproblem (Q_7, G_7).

Coordinate order: index 3p+j, p = centre (0, log2, log3), j = profile (phi_0,phi_1,phi_2).
Moment rows (common factor m_eta removed):  r_+ = e^{x_p/2}(1,-1/2,0),  r_- = e^{-x_p/2}(1,1/2,0).
With u_p = a_p - b_p/2, v_p = a_p + b_p/2 the two constraints decouple:
   sum_p e^{x_p/2} u_p = 0 ,  sum_p e^{-x_p/2} v_p = 0 ,
so kernel = {u perp (1,sqrt2,sqrt3)} + {v perp (1,1/sqrt2,1/sqrt3)} + free phi_2 block.
"""
import sympy as sp

s2, s3 = sp.sqrt(2), sp.sqrt(3)

def kernel_basis():
    """9x7 exact matrix; column 0 is the mean vector z (x) (1,0,0), z=(-1,2sqrt2,-sqrt3)."""
    def vec(a, b, c):
        out = []
        for p in range(3):
            out += [a[p], b[p], c[p]]
        return sp.Matrix(out)
    def from_uv(u, v):
        a = [sp.Rational(1,2)*(u[p]+v[p]) for p in range(3)]
        b = [v[p]-u[p] for p in range(3)]
        return vec(a, b, [0,0,0])
    z = [-1, 2*s2, -s3]
    cols = [
        vec(z, [0,0,0], [0,0,0]),                 # B1 : the mean direction z (x) (1,0,0)
        from_uv([s2, -1, 0], [0,0,0]),            # B2
        from_uv([s3, 0, -1], [0,0,0]),            # B3
        from_uv([0,0,0], [1, -s2, 0]),            # B4
        vec([0,0,0],[0,0,0],[1,0,0]),             # B5 = e_{0,2}
        vec([0,0,0],[0,0,0],[0,1,0]),             # B6 = e_{1,2}
        vec([0,0,0],[0,0,0],[0,0,1]),             # B7 = e_{2,2}
    ]
    return sp.Matrix.hstack(*cols)

def moment_rows():
    sp_ = [1, s2, s3]
    rp = []; rm = []
    for p in range(3):
        rp += [sp_[p], -sp_[p]*sp.Rational(1,2), 0]
        rm += [1/sp_[p], sp.Rational(1,2)/sp_[p], 0]
    return sp.Matrix([rp]), sp.Matrix([rm])

if __name__ == '__main__':
    K = kernel_basis(); rp, rm = moment_rows()
    print('rank K =', K.rank(), ' (must be 7)')
    print('rank [r+;r-] =', sp.Matrix.vstack(rp, rm).rank(), ' (must be 2)')
    print('r+ K =', sp.simplify(rp*K).T.T)
    print('r- K =', sp.simplify(rm*K).T.T)
    print('K ='); sp.pprint(K.T)
