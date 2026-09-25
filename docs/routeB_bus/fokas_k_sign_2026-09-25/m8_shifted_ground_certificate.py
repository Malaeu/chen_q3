#!/usr/bin/env python3
"""Finite rational-reference m8 certificate with an independent energy shift.

Not a certificate on the selected cofinal family. No approximate eigenvalue
or floating-point eigenvector is a premise of the certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path
from flint import arb, acb, acb_mat
import m8_negative_certificate as source

HERE = Path(__file__).resolve().parent


def inner(x, y):
    return sum((a.conjugate()*b for a,b in zip(x,y)), acb(0))


def real(x):
    x = acb(x)
    if not x.imag.contains(0):
        raise ArithmeticError(f'expected real exact quantity: {x}')
    return x.real


def inertia(A):
    """Interval Hermitian LDL*: every real pivot must exclude zero."""
    n=len(A); L=[[acb(int(i==j)) for j in range(n)] for i in range(n)]
    ds=[]; signs=[]
    for j in range(n):
        dj=real(acb(A[j][j])-sum((L[j][k]*L[j][k].conjugate()*ds[k]
                                   for k in range(j)),acb(0)))
        if dj>0: signs.append(1)
        elif dj<0: signs.append(-1)
        else: raise ArithmeticError(f'inconclusive pivot {j}: {dj}')
        ds.append(dj)
        for i in range(j+1,n):
            L[i][j]=(acb(A[i][j])-sum((L[i][k]*L[j][k].conjugate()*ds[k]
                                      for k in range(j)),acb(0)))/dj
    return {'negative':signs.count(-1),'positive':signs.count(1),
            'pivot_signs':signs,'pivot_enclosures':[d.str(65) for d in ds]}


def certify(dps):
    K,q,a=source.build_data(dps=dps)
    n=len(q);mu=arb('1e-18');delta=arb('3e-17')
    Kq=[sum((K[i][j]*q[j] for j in range(n)),acb(0)) for i in range(n)]
    r=[Kq[i]-a*q[i] for i in range(n)]
    # C=Q(K-mu I)Q+qq*, Q=I-qq*. Exact q has norm one by construction.
    C=[[acb(K[i][j])-mu*int(i==j)-q[i]*Kq[j].conjugate()
        -Kq[i]*q[j].conjugate()+(a+mu+1)*q[i]*q[j].conjugate()
        for j in range(n)] for i in range(n)]
    ki=inertia([[acb(K[i][j])-mu*int(i==j) for j in range(n)] for i in range(n)])
    ci=inertia([[C[i][j]-delta*int(i==j) for j in range(n)] for i in range(n)])
    cluster_low=arb('1e-12');cluster_high=arb('1e-10')
    low_i=inertia([[acb(K[i][j])-cluster_low*int(i==j) for j in range(n)] for i in range(n)])
    high_i=inertia([[acb(K[i][j])-cluster_high*int(i==j) for j in range(n)] for i in range(n)])
    if low_i['negative']!=4 or high_i['negative']!=4:
        raise ArithmeticError('four-level external cluster gap not verified')
    if ki['negative']!=1 or ci['positive']!=n:
        raise ArithmeticError('required inertia certificates failed')
    # LU ball solve; never algorithm="approx".
    v=acb_mat(C).solve(acb_mat([[x] for x in r]),algorithm='lu')
    vs=[v[i,0] for i in range(n)]
    R2=real(inner(vs,vs));R=R2.sqrt();angle=(R2/(1+R2)).sqrt()
    if not (R<arb('0.05544') and angle<arb('0.05536')):
        raise ArithmeticError('claimed angle budget not verified')
    result={
      'status':'CERTIFIED_FINITE_RATIONAL_REFERENCE_CELL_ONLY',
      'm':8,'decimal_precision':dps,
      'scope':'exact rational energy points defined by m8_negative_certificate.build_data; not exact selected energies or a cofinal statement',
      'mu':mu.str(65),'certified_complement_floor_delta':delta.str(65),
      'rayleigh_a':a.str(65),'K_minus_mu_inertia':ki,
      'C_mu_minus_delta_I_inertia':ci,
      'K_minus_1e_minus12_inertia':low_i,'K_minus_1e_minus10_inertia':high_i,
      'first_four_eigenvalues_below':'1e-12','remaining_eigenvalues_above':'1e-10',
      'certified_external_cluster_gap_lower':'9.9e-11',
      'q_norm_squared_enclosure':real(inner(q,q)).str(65),
      'q_star_residual_enclosure':str(inner(q,r)),
      'R_mu_squared':R2.str(65),'R_mu':R.str(65),
      'ground_projection_error_upper_enclosure':angle.str(65),
      'rigorous_rational_projection_error_upper':'0.05536',
      'proof':'K-muI has exactly one negative eigenvalue; C_mu-deltaI positive definite proves B_mu>=deltaI. The independent-shift inverse-residual theorem then gives the projection-error bound.',
      'no_claims':['cofinal floor','selected exact-energy row applicability','real-zero family','compact tracking decay','RH'],
      'sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
                  [Path(__file__),HERE/'m8_negative_certificate.py',HERE/'arb_m2_certificate.py',HERE/'schur_probe_m8_dps140.json']},
    }
    out=HERE/f'm8_shifted_ground_certificate_dps{dps}.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','mu','certified_complement_floor_delta','rayleigh_a','R_mu','ground_projection_error_upper_enclosure']},indent=2))
    print(out)


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--dps',type=int,default=100)
    certify(ap.parse_args().dps)
