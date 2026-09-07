"""Verification and diagnostics for the packet certificate.

  A  weakest combinations: eigenvectors of the pencil (F, H). FLOAT, DIAGNOSTIC_NEVER_A_PROOF --
     only the certified lambda_min of packassemble.py is a statement; the eigenvector says which
     direction is weak.  The Rayleigh quotient of that vector, evaluated in balls, is a rigorous
     UPPER bound for lambda_min and brackets the certificate.
  B  second quadrature: band [0,1000] under two entirely different rules.
  C  h4 diagonal vs the earlier scalar certificate [0.0034393623, 0.0035782034].

Usage: packverify.py main_raw [xcheck_raw]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, ctx
import numpy as np
import scipy.linalg as sla
import packassemble as PA

PREC = 400


def fmid(M):
    return np.array([[float(M[i][j].mid().str(20, radius=False)) for j in range(len(M))]
                     for i in range(len(M))])


def main():
    raw = sys.argv[1]
    X = 4000.0
    F0, RF, Hm, H0, RH, lams = PA.main(raw, X, 90)
    ctx.prec = PREC
    NAMES = PA.NAMES

    print("\n" + "=" * 104)
    print("A. WEAKEST COMBINATIONS  (float eigenvectors; DIAGNOSTIC_NEVER_A_PROOF)")
    for tag, idx in (("span3 {h4,h5,h6}", PA.SPAN3), ("span4 {h4,h5,h6,h7}", PA.SPAN4)):
        Ff = fmid(PA.sub(F0, idx)); Hf = fmid(PA.sub(H0, idx))
        ev, V = sla.eigh(Ff, Hf)
        nm = [NAMES[i] for i in idx]
        print(f"  {tag}: pencil eigs = {np.array2string(ev, precision=8)}")
        print(f"     eig(F) = {np.array2string(np.linalg.eigvalsh(Ff), precision=5)}"
              f"   eig(H) = {np.array2string(np.linalg.eigvalsh(Hf), precision=4)}")
        for k in range(len(idx)):
            v = V[:, k] / np.max(np.abs(V[:, k]))
            lab = "weakest " if k == 0 else f"mode {k}  "
            print(f"     {lab} " + "  ".join(f"{n}:{c:+.5f}" for n, c in zip(nm, v)))
        v = V[:, 0] / np.max(np.abs(V[:, 0]))
        c = [arb(float(x)) for x in v]
        Fb = [[arb(F0[i][j].mid(), RF[i][j]) for j in idx] for i in idx]
        ub = PA.rayleigh(Fb, PA.sub(Hm, idx), c).abs_upper()
        lam = lams[tag.split()[0]]
        lo = "NOT CERTIFIED" if lam is None else (lam.mid() - lam.rad()).str(12)
        print(f"     certified bracket:  {lo}  <=  lambda_min  <=  {ub.str(12, radius=False)}")

    print("\n" + "=" * 104)
    print("B. SECOND QUADRATURE, band [0,1000], different node set")
    if len(sys.argv) > 2 and os.path.exists(sys.argv[2]):
        t1 = open(raw).read(); t2 = open(sys.argv[2]).read()
        allok = True
        for i in range(len(NAMES)):
            for j in range(i, len(NAMES)):
                a, ar = PA.read_mr(t1, f"I_band1000[{NAMES[i]},{NAMES[j]}]")
                b, br = PA.read_mr(t2, f"I_compact[{NAMES[i]},{NAMES[j]}]")
                A = arb(a.mid(), ar); B = arb(b.mid(), br)
                ok = A.overlaps(B); allok &= ok
                print(f"  {NAMES[i]+','+NAMES[j]:12s} main={A.str(18):>26s}  "
                      f"xcheck={B.str(18):>26s}  |diff|<={(A-B).abs_upper().str(4)}  overlap={ok}")
        print(f"  ALL OVERLAP: {allok}")
    else:
        print("  (xcheck raw file not supplied)")

    print("\n" + "=" * 104)
    print("C. h4 DIAGONAL vs the earlier scalar certificate")
    i4 = NAMES.index("h4")
    q = arb(F0[i4][i4].mid(), RF[i4][i4]) / Hm[i4][i4]
    lo = q.mid() - q.rad(); lo = lo.mid() - lo.rad(); hi = q.mid() + q.rad(); hi = hi.mid() + hi.rad()   # signed directed endpoints
    L0 = arb("0.0034393623002774739205"); U0 = arb("0.0035782034198665259817")
    print(f"  packet F_44/H_44 = [{lo.str(18, radius=False)}, {hi.str(18, radius=False)}]")
    print(f"  h4 certificate   = [{L0.str(18)}, {U0.str(18)}]")
    print(f"  contained in the earlier interval: {bool(lo > L0) and bool(hi < U0)}"
          f"   width ratio = {float(((U0-L0)/(hi-lo)).str(6, radius=False)):.1f}x tighter")


if __name__ == '__main__':
    main()
