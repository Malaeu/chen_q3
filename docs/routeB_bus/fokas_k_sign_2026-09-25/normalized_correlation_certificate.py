"""Arb m=2 reference: full normalized correlation is not pointwise positive.
Uses the frozen source/plane enclosures of arb_m2_certificate.py.
No cofinal or ground-tracking claim. Run from repo with .venv/bin/python.
"""
import json
import arb_m2_certificate as c


def run():
    c.ctx.dps = 100
    F = c.source_F()
    Pi, *_ = c.gaussian_plane(cutoff=12)
    z = c.z_from_energies(F, c.source_energy_ball(0), c.source_energy_ball(4))
    p = c.matvec(Pi, z)
    X2, Y2 = c.inner(z, z).real, c.inner(p, p).real
    assert X2.lower() > 0 and Y2.lower() > 0
    def sum_square(w):
        s = sum(w, c.acb(0))
        return (s.conjugate()*s).real
    A = (sum((sum(row, c.arb(0)) for row in Pi), c.arb(0))
         - sum_square(p)/Y2 - sum_square(z)/X2)
    endpoint = A/c.arb(2).log()
    # Q(L/2) is exactly diag((-1)^n): the off-diagonal sines vanish.
    D = [c.arb((-1)**n) for n in c.MODES]
    delta_half = (sum((Pi[i][i]*D[i] for i in range(len(D))), c.arb(0))
                  - c.inner(p, [D[i]*p[i] for i in range(len(D))]).real/Y2
                  - c.inner(z, [D[i]*z[i] for i in range(len(D))]).real/X2)
    assert endpoint.lower() > 0
    assert delta_half.upper() < 0
    return {
        "scope": "m=2 full rational energy rectangle from frozen certificate",
        "precision_dps": c.ctx.dps,
        "endpoint_h_Delta_limit": str(endpoint),
        "Delta_at_L_over_2": str(delta_half),
        "h_at_L_over_2_positive": "t=sqrt(2); t^3-t-1=sqrt(2)-1>0",
        "verdict": "POINTWISE_DENSITY_POSITIVITY_FAILS_IN_REFERENCE_CELL",
        "cofinal_conclusion": "NONE",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
