"""Verification for the Legendre packet certificate.

  V1  mass identity per test (also load-bearing: it supplies E_freq) -- printed by legassemble.
  V2  h_0 = h_4 exactly (P_0 = 1), so the L0 row of this run must reproduce, panel-sum for
      panel-sum, the h4 row of the ratified packet run at the same X, WID, NCC -- with a
      DIFFERENT moment evaluator (integration-by-parts recursion here, entire power series
      there).  Also compared against the earlier scalar certificate interval.
  V3  second quadrature on [0,1000] under an entirely different rule (w=0.4, n=28).
  V4  cross-parity vanishing: for a same-block pair the integrand is even, for a cross-parity
      pair it is ODD, so the entry vanishes exactly.  Checked at real nodes by evaluating the
      full integrand at +xi and -xi.
  V5  Parseval/pole identities -- printed by legarb.py.

Usage: legverify.py X xcheck_raw main_raw1 [main_raw2 ...]
"""
import sys, os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, acb, ctx
import legarb, legassemble as LA, legser

PREC = 400
PACKET_MAIN = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                           "packet", "out", "main.txt")
H4_SCALAR_LO = "0.0034393623002774739205"
H4_SCALAR_HI = "0.0035782034198665259817"
H4_PACKET_DIAG_LO = "0.0035085369"
H4_PACKET_DIAG_HI = "0.0035090288"


def main():
    X = float(sys.argv[1])
    xck = sys.argv[2]
    mains = sys.argv[3:]
    texts = [open(p).read() for p in mains]
    ctx.prec = PREC

    print("=" * 108)
    print("V2. h_0 = h_4  (P_0 = 1): this run's L0 row vs the ratified packet's h4 row")
    if os.path.exists(PACKET_MAIN):
        pk = open(PACKET_MAIN).read()
        band0 = open(mains[0]).read()          # the [0,4000] band, same rule as the packet run
        for key_l, key_p in (("I_compact[L0,L0]", "I_compact[h4,h4]"),
                             ("MASS[L0]", "MASS[h4]")):
            a, ar = LA.read_mr(band0, key_l)
            b, br = LA.read_mr(pk, key_p)
            A = arb(a.mid(), ar); B = arb(b.mid(), br)
            print(f"   {key_l:20s} = {A.str(20):>26s}   packet {key_p:18s} = {B.str(20):>26s}"
                  f"   overlap={bool(A.overlaps(B))}  |diff| <= {(A-B).abs_upper().str(4)}")
    else:
        print("   (packet raw output not present)")

    S = LA.build(X, 90, texts, LA.EBASE_DEF, LA.EBASEM_DEF)
    F0, RF, H, H0, RH = LA.block(S, legarb.EVEN)
    q = arb(F0[0][0].mid(), RF[0][0]) / H[0][0]
    print(f"\n   F_00/H_00 = [{legser.dec_lower(q,14)}, {legser.dec_upper(q,14)}]")
    print(f"   packet h4 diagonal      = [{H4_PACKET_DIAG_LO}, {H4_PACKET_DIAG_HI}]"
          f"   contained: {bool(LA.lb(q) > arb(H4_PACKET_DIAG_LO)) and bool(LA.ub(q) < arb(H4_PACKET_DIAG_HI))}")
    print(f"   h4 scalar certificate   = [{H4_SCALAR_LO}, {H4_SCALAR_HI}]"
          f"   contained: {bool(LA.lb(q) > arb(H4_SCALAR_LO)) and bool(LA.ub(q) < arb(H4_SCALAR_HI))}")

    print("\n" + "=" * 108)
    print("V3. SECOND QUADRATURE, band [0,1000], different node set (w=0.4, n=28 vs w=0.5, n=36)")
    if os.path.exists(xck):
        t2 = open(xck).read()
        t1 = open(mains[0]).read()
        allok = True
        for i in range(8):
            for j in range(i, 8):
                if (i + j) % 2:
                    continue
                key = f"[{legarb.NAMES[i]},{legarb.NAMES[j]}]"
                a, ar = LA.read_mr(t1, "I_band1000" + key)
                b, br = LA.read_mr(t2, "I_compact" + key)
                A = arb(a.mid(), ar); B = arb(b.mid(), br)
                ok = A.overlaps(B); allok &= ok
                print(f"   {legarb.NAMES[i]+','+legarb.NAMES[j]:10s} main={A.str(18):>26s}  "
                      f"xcheck={B.str(18):>26s}  |diff|<={(A-B).abs_upper().str(4)}  ok={ok}")
        print(f"   ALL OVERLAP: {allok}")
    else:
        print("   (xcheck raw file not present)")

    print("\n" + "=" * 108)
    print("V4. CROSS-PARITY ENTRIES VANISH EXACTLY (integrand odd; b = w_a ell_2 real and even)")
    import evalf
    C = evalf.Ctx(PREC)
    d, A = legarb.profiles(PREC)
    worst = arb(0)
    for xiv in ("3.7", "41.3", "377.9", "1913.1"):
        ctx.prec = 12000            # node balls must be far finer than the e^beta cancellation
        xi = arb(xiv)
        ctx.prec = PREC
        tot = arb(0)
        ells = []
        for sg in (1, -1):
            z = sg * xi
            t2_, g2_, _ = evalf.t2_and_gamma(z, C, PREC)
            ctx.prec = PREC
            ell = 2 * (g2_ * t2_).real
            ells.append(ell)
            wa = 1 - (C.a * z).cos()
            gv = legarb.hprofiles(acb(z), d, A, PREC)
            # cross-parity representative (L0, L1): conj(hhat_0) hhat_1 = -i g_0 g_1,
            # the real integrand of that entry is Im-part-free; its value at +xi and -xi
            # must cancel because g_0 is even and g_1 is odd in xi.
            tot += -wa * ell * gv[0] * gv[1]
        if tot.abs_upper() > worst:
            worst = tot.abs_upper()
        print(f"   xi = {xiv:>8s}:  |ell_2(xi) - ell_2(-xi)| <= {(ells[0]-ells[1]).abs_upper().str(4)}"
              f"    integrand(+xi) + integrand(-xi) = {tot.str(6)}")
    print(f"   worst |sum| = {worst.str(6)}  (exact cancellation; the cross-parity entries were"
          f" never computed)")
    print("   parity of the eight profiles (g_j even/odd in xi):")
    ctx.prec = 12000
    xp, xm = arb("17.25"), arb("-17.25")
    ctx.prec = PREC
    for j in range(8):
        gp = legarb.hprofiles(acb(xp), d, A, PREC)[j]
        gm = legarb.hprofiles(acb(xm), d, A, PREC)[j]
        par = "even" if bool((gp - gm).abs_upper() < arb(10) ** -100) else (
            "odd" if bool((gp + gm).abs_upper() < arb(10) ** -100) else "MIXED")
        print(f"      {legarb.NAMES[j]}: {par}   (expected {'even' if j%2==0 else 'odd'})")


if __name__ == '__main__':
    main()
