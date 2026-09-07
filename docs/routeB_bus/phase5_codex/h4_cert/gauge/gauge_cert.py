"""RIGOROUS (arb ball) certificate for  p(xi) + FT(chi R_g)(xi) >= 0  for all real xi,
R_g = R + 2 alpha cosh(t/2) the pole-gauged remainder of the Schur kernel identity (6),
chi the fixed quintic-smoothstep cutoff of the verdict (=1 on [-2d,2d], 0 outside (-d0,d0)).

Certificate (two constants, no band scan):
  A := ||chi R_g||_{L1(R)}      => |F(xi)| <= A            covers |xi| <= 2pi  (p >= c_*/(2pi+|xi|) >= c_*/(4pi))
  B := ||(chi R_g)'||_{L1(R)}   => |F(xi)| <= B/|xi|       covers |xi| >= 2pi  (p >= c_*/|xi|)
  PASS iff  A < c_*/(4pi)  and  B < c_*.

Region I  t in [0,t2]:  analytic bounds (near-origin oscillation of q'_beta is not
                        resolvable by ball evaluation; see report Lemma 3).
Region II t in [t2,d0]: graded grid, ball enclosures of R and R'.
"""
import sys, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb
from gauge_cert_core import setup, K, Lpair, R_and_Rp, QQ, GG, NT

PREC   = int(os.environ.get('PREC', 300))
JN     = int(os.environ.get('JN', 24))
PHI    = arb(os.environ.get('PHI', '0.0015'))      # relative cell half-width in region II
T2EXP  = int(os.environ.get('T2EXP', 3))           # region I is [0, 1e-T2EXP]
ALPHA_N, ALPHA_D = 519, 1000                       # FIXED before the rigorous run
OUT    = os.environ.get('OUT', '/home/chirurgie/.claude/jobs/4b35770d/tmp/gauge_cert/out')

setup(PREC); KK = K()
a, d0, dl, c, pi, r2 = KK['a'], KK['d0'], KK['delta'], KK['c'], KK['pi'], KK['r2']
cstar, kap, E, Bx = KK['cstar'], KK['kappa'], KK['E'], KK['Bx']
alpha = arb(ALPHA_N)/ALPHA_D
two_dl = 2*dl
t2 = arb(10)**(-T2EXP)
def flt(x): return float(arb(x).mid())

# ================= REGION I : t in [0,t2], analytic ==========================
# |q'_beta(s)| <= B1 = 0.5453 + 0.3231 b^2 s^2
#              <= B2 = 1.2507 + 16.693/(b|s|)
#              <= B3 = 13.917/(b|s|) + 10.933/(b s^2)
def region1_Q():
    tot = arb(0)
    for j in range(0, 400):
        b = 2*pi*arb(2)**j
        s1 = 1/b;              s1 = t2 if s1 > t2 else s1
        s2 = arb('3.1')/b.sqrt(); s2 = t2 if s2 > t2 else s2
        if s2 < s1: s2 = s1
        I  = arb('0.5453')*s1 + arb('0.1077')*b**2*s1**3
        if s2 > s1:
            I = I + arb('1.2507')*(s2-s1) + arb('16.693')/b*(s2/s1).log()
        if t2 > s2:
            I = I + arb('13.917')/b*(t2/s2).log() + arb('10.933')/b*(1/s2 - 1/t2)
        tot = tot + 2*I                      # |w_b| <= |q'(t)|+|q'(-t)|
    # GAUGE verdict (G26): the omitted dyadic tail j >= 400 of int_0^{t2}|w_b|, via SCHUR (8) ||q_b||_{W^{1,1}} <= 2048 b^{-1/2}:
    # eps_Q <= (2048/sqrt(2 pi)) * 2^{-200} / (1 - 2^{-1/2}) < 2^{-188}; added as a ball radius (positive majorant, never dropped).
    epsQ = (arb(2048)/(2*pi).sqrt()) * arb(2)**(-200) / (1 - 1/arb(2).sqrt())
    tot = tot + arb(0, epsQ.upper())
    return tot
tb1 = arb(0, t2.upper())                     # the ball [-t2, t2]
G1, Gp1 = GG(tb1, KK)
N1, Np1 = NT(tb1, JN, KK)
IQ1 = region1_Q()
V1  = c/2*IQ1 + r2/4*t2*Gp1.abs_upper() + 2*pi*t2*Np1.abs_upper()     # >= int_0^{t2}|R'|
Rgt2_hi = None                                                        # filled after region II
B_I = 2*(V1 + alpha*t2*(t2/2).sinh())

# ================= REGION II : graded grid ===================================
rho = (1+PHI)/(1-PHI)
nodes = [t2]
while nodes[-1] < two_dl:
    nx = nodes[-1]*rho
    if nx >= two_dl: break
    nodes.append(nx)
nodes.append(two_dl)
while nodes[-1] < d0:
    nx = nodes[-1]*rho
    if nx >= d0: break
    nodes.append(nx)
nodes.append(d0)

def chi_pair(tb, tl, tr):
    if tr <= two_dl: return arb(1), arb(0)
    x = (tb - two_dl)/(d0 - two_dl)
    return 1 - (10*x**3 - 15*x**4 + 6*x**5), -30*x**2*(1-x)**2/(d0 - two_dl)

Asum = arb(0); Bsum = arb(0); rows = []
Rg_at_t2 = None
t0 = time.time()
for k in range(len(nodes)-1):
    tl, tr = nodes[k], nodes[k+1]
    # GAUGE verdict §3.5: explicit endpoint hull (the midpoint/half-width constructor does not contain the outer hull for
    # arbitrary endpoint balls). lo/hi are the outer endpoints of the node balls; tb encloses [lo, hi] by construction.
    lo = tl.mid() - tl.rad(); hi = tr.mid() + tr.rad()
    tb = arb((lo + hi)/2) + arb(0, ((hi - lo)/2).upper()); w = arb((hi - lo).upper())
    Jq = 8
    while (arb(2)**(-Jq)/(2*pi)*(arb('4.76')/tl + arb('25.4')/(tl*tl))) > arb(10)**-9:
        Jq += 4
    R, Rp = R_and_Rp(tb, tl, Jq, JN, KK)
    Rg  = R  + 2*alpha*(tb/2).cosh()
    Rgp = Rp + alpha*(tb/2).sinh()
    if k == 0: Rg_at_t2 = Rg.abs_upper()
    ch, chp = chi_pair(tb, tl, tr)
    aI = 2*w*(ch*Rg).abs_upper()
    bI = 2*w*(chp*Rg + ch*Rgp).abs_upper()
    Asum += aI; Bsum += bI
    rows.append((flt(tl), flt(tr), Jq, R.str(14), Rp.str(14), flt(aI), flt(bI)))
el = time.time()-t0

A_I = 2*t2*(arb(Rg_at_t2) + V1 + alpha*t2*(t2/2).sinh())   # |R_g| <= |R_g(t2)| + int|R_g'| on [0,t2]; the gauge term's derivative added (check defect b)
Aup = arb((A_I + Asum).upper()); Bup = arb((B_I + Bsum).upper())
thrA = cstar/(4*pi); thrB = cstar
okA = Aup < thrA; okB = Bup < thrB

os.makedirs(OUT, exist_ok=True)
with open(os.path.join(OUT,'gauge_cert.txt'),'w') as f:
    def W(s): f.write(s+"\n"); print(s, flush=True)
    W(f"# GAUGE POSITIVE-EXTENSION CERTIFICATE  arb prec={PREC} JN={JN} phi={PHI.str(6)} cells={len(nodes)-1} {el:.0f}s")
    W(f"alpha  = {ALPHA_N}/{ALPHA_D}")
    for nm,v in (('a',a),('d0',d0),('delta',dl),('c',c),('c_*',cstar),('kappa',kap)):
        W(f"{nm:7s}= {v.str(25)}")
    W(f"REGION I  [0,{flt(t2):.0e}]  sum_j int|w_b| <= {IQ1.str(8)}   V1=int|R'| <= {V1.str(8)}")
    W(f"          A_I <= {A_I.str(8)}    B_I <= {B_I.str(8)}")
    W(f"REGION II [{flt(t2):.0e},d0]  A_II <= {Asum.str(10)}   B_II <= {Bsum.str(10)}")
    W(f"A = ||chi R_g||_1     <= {Aup.str(12)}")
    W(f"B = ||(chi R_g)'||_1  <= {Bup.str(12)}")
    W(f"thr A = c_*/(4pi) = {thrA.str(12)}   A/thr = {flt(Aup/thrA):.6f}   {'PASS' if okA else 'FAIL'}")
    W(f"thr B = c_*       = {thrB.str(12)}   B/thr = {flt(Bup/thrB):.6f}   {'PASS' if okB else 'FAIL'}")
    W(f"crude Lpair fallbacks: {Lpair.fallback}")
    W("RESULT: " + ("GAUGE_SOURCE_POSITIVE_EXTENSION_CERTIFIED" if (okA and okB) else "NOT_CERTIFIED"))
    W("")
    W("# ledger: tl tr Jq R Rp dA dB")
    for r in rows: W("%.6e %.6e %3d %s %s %.4e %.4e" % r)
print("wrote", os.path.join(OUT,'gauge_cert.txt'))
