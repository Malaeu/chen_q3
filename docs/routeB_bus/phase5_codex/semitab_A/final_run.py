import numpy as np, time, json, sys
from run_table import ops, geom, build_A, carrier_EN, E_spec
from core import Test, D_minus_cA, prime_sum, primes_upto, C_A
import tests_family as TF

H = TF.HALF; SH = np.log(2.0)/2

def mk(name, fun, half, ngl=1200, cx=False):
    return name, Test(fun, half, name, ngl=ngl, complex_=cx)

TESTS = []
for b in [0.05, 0.1, 0.2, 0.3, 0.5]:
    TESTS.append(mk(f"gauss b={b}", TF.gauss_bump(b, H), H, 1600))
hn = H-SH
for b in [0.1, 0.2]:
    TESTS.append(mk(f"gauss b={b} @+log2/2", (lambda bb: (lambda x: TF.gauss_bump(bb, hn)(x-SH)))(b), H, 1600))
    TESTS.append(mk(f"gauss b={b} @-log2/2", (lambda bb: (lambda x: TF.gauss_bump(bb, hn)(x+SH)))(b), H, 1600))
for b in [0.1, 0.2]:
    TESTS.append(mk(f"2bump b={b} (+)", (lambda bb: (lambda x: TF.gauss_bump(bb, hn)(x-SH)+TF.gauss_bump(bb, hn)(x+SH)))(b), H, 1600))
    TESTS.append(mk(f"2bump b={b} (-)", (lambda bb: (lambda x: TF.gauss_bump(bb, hn)(x-SH)-TF.gauss_bump(bb, hn)(x+SH)))(b), H, 1600))
for w in [2, 5, 10]:
    TESTS.append(mk(f"gauss b=0.2 e^(i{w}x)", (lambda ww: (lambda x: TF.gauss_bump(0.2, H)(x)*np.exp(1j*ww*x)))(w), H, 2000, True))
for sg, lbl in [('+', 'v+'), ('-', 'v-'), ('i', 'vi')]:
    fun, h = TF.polebump(sg)
    TESTS.append(mk(f"pole-null {lbl}", fun, h, 2000, sg == 'i'))
for b in [3, 4, 6]:
    fun, h = TF.wide(b)
    TESTS.append(mk(f"wide cos b={b}", fun, h, 3000))
for R in [0.5, 1.0, 2.0]:
    fun, h = TF.vR(R)
    TESTS.append(mk(f"v_R R={R}", fun, h, 3000))

ALLP = primes_upto(200000)
def quad_quantities(T):
    Darch = D_minus_cA(T)
    ps2 = prime_sum(T, (2,))
    psall = prime_sum(T, ALLP)
    LS = Darch-ps2
    Q = Darch+T.P02-psall
    return dict(nrm2=T.nrm2, Darch=Darch, ps2=ps2, psall=psall, LS=LS, P02=T.P02, Q=Q)

def rich(v1, v2):        # O(delta) Richardson, delta halved from run1 to run2
    return 2*v2-v1

if __name__ == "__main__":
    lam = 1.0; Ns = (800, 3200)
    for N in Ns: ops(N)
    C0, _, dg = ops(3200)
    print("CARRIER DIAG", json.dumps(dg), flush=True)
    for key in ['arch', 'src', 'pol']:
        g = geom(3200, lam, key)
        print(f"GEOM {key} lam=1 N=3200: m={g['m']} rankPi={g['rankPi']} commonkernel_dim={g['nker']} "
              f"nblk(|alpha|>1e-6)={g['nblk']} alpha[:8]={np.array2string(g['alpha'][:8],precision=7)}", flush=True)
    rows = []
    for name, T in TESTS:
        t0 = time.time()
        qq = quad_quantities(T)
        span = 2*T.half
        rec = dict(name=name, **qq, span=span)
        xr = dg['xrange'][1]-dg['xrange'][0]
        rec['representable'] = bool(span < 0.75*xr)
        if rec['representable']:
            res = {}
            for N in Ns:
                Cc, _, _ = ops(N); A = build_A(Cc, T)
                for key in ['arch', 'src', 'pol']:
                    r = carrier_EN(N, lam, key, T, A)
                    res[(key, N)] = r
                del A
            for key in ['arch', 'src', 'pol']:
                rec[f'E_{key}'] = rich(res[(key, Ns[0])]['E_S'], res[(key, Ns[1])]['E_S'])
                rec[f'N_{key}'] = rich(res[(key, Ns[0])]['N_S'], res[(key, Ns[1])]['N_S'])
                rec[f'E_{key}_raw'] = [res[(key, n)]['E_S'] for n in Ns]
                rec[f'N_{key}_raw'] = [res[(key, n)]['N_S'] for n in Ns]
            try:
                es, _ = E_spec(lam, T); rec['E_spec_arch'] = es
            except Exception as e:
                rec['E_spec_arch'] = None
        rows.append(rec)
        print(f"DONE {name}  [{time.time()-t0:.0f}s]  ||v||^2={qq['nrm2']:.6g} LS={qq['LS']:.6g} Q={qq['Q']:.6g} "
              f"E_pol={rec.get('E_pol','--')} N_pol={rec.get('N_pol','--')}", flush=True)
        json.dump(rows, open("rows_lam1.json", "w"), indent=1, default=float)
