from __future__ import annotations
import json, time
from pathlib import Path
import mpmath as mp
ROOT = Path(__file__).parent
seeds = [("0.808517", "85.69935"), ("0.650830", "114.16334"),
         ("0.869531", "240.40467"), ("0.574356", "166.47931")]
def dh(s):
    c = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
    coeff = (mp.mpf(1), c, -c, mp.mpf(-1))
    return mp.power(5, -s) * sum(a * mp.zeta(s, mp.mpf(k)/5)
                               for k, a in enumerate(coeff, 1))
def completion(s):
    return mp.power(5/mp.pi, s/2) * mp.gamma((s+1)/2) * dh(s)
def M_dh(z):
    s = mp.mpf("0.5") - 1j*z
    return 1j * (mp.log(5/mp.pi)/2 + mp.digamma((s+1)/2)/2 + mp.diff(dh, s)/dh(s))
def M_zeta(z):
    s = mp.mpf("0.5") - 1j*z
    return 1j*(1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2
                + mp.zeta(s, derivative=1)/mp.zeta(s))
def defect(M, z):
    v = M(z)
    S = (v-1j)/(v+1j)
    direct = abs(S)**2-1
    identity = -4*mp.im(v)/abs(v+1j)**2
    return direct, abs(direct-identity)
def nstr(x): return mp.nstr(x, 32)
records = []
start = time.monotonic()
for dps in (45, 70):
    mp.mp.dps = dps
    for index, (beta, gamma) in enumerate(seeds, 1):
        rho = mp.findroot(dh, mp.mpc(beta, gamma), tol=mp.mpf(10)**(-dps+8), maxsteps=40)
        w = mp.mpc(mp.im(rho), mp.re(rho)-mp.mpf("0.5"))
        row = {"dps":dps, "kind":"DH", "beta":nstr(mp.re(rho)), "gamma":nstr(mp.im(rho)),
               "root_residual":nstr(abs(dh(rho))), "samples":[]}
        s = rho + mp.mpf("0.03")
        fa, fb = completion(s), completion(1-s)
        row["functional_equation_relative_error"] = nstr(abs(fa-fb)/max(abs(fa),abs(fb)))
        row["real_axis_DH_defect"] = nstr(defect(M_dh, mp.re(w))[0])
        row["real_axis_zeta_defect"] = nstr(defect(M_zeta, mp.re(w))[0])
        for eps_s in ("0.001", "0.0001"):
            eps = mp.mpf(eps_s)
            z = w-1j*eps
            dd, err = defect(M_dh, z)
            dz, _ = defect(M_zeta, z)
            dc, _ = defect(lambda z: mp.log(3)*mp.tan(mp.log(3)*z), z)
            row["samples"].append({"epsilon":eps_s, "DH_defect":nstr(dd),
                                   "ratio_to_4eps":nstr(dd/(4*eps)),
                                   "zeta_control_defect":nstr(dz),
                                   "curve_control_defect":nstr(dc),
                                   "defect_identity_error":nstr(err)})
        records.append(row)
        done = (0 if dps == 45 else 5) + index
        eta = (time.monotonic()-start)*(10-done)/done
        print(f"[{'#'*done}{'.'*(10-done)}] {done}/10 ETA {eta:.1f}s", flush=True)
    w = mp.mpc(7, mp.mpf(1)/3)
    poles = (w, -w, w.conjugate(), -w.conjugate())
    def M_plant(z): return M_zeta(z) - sum(1/(z-v) for v in poles)
    row = {"dps":dps,"kind":"PLANTED","w":"7+i/3", "samples":[],
           "real_axis_defect":nstr(defect(M_plant, mp.mpf(7))[0])}
    for eps_s in ("0.001", "0.0001"):
        eps = mp.mpf(eps_s)
        dd, err = defect(M_plant, w-1j*eps)
        row["samples"].append({"epsilon":eps_s, "defect":nstr(dd),
                               "ratio_to_4eps":nstr(dd/(4*eps)),
                               "defect_identity_error":nstr(err)})
    records.append(row)
    print(f"[{'#'*(5 if dps==45 else 10)}{'.'*(5 if dps==45 else 0)}] {(5 if dps==45 else 10)}/10", flush=True)
(ROOT/'diag_results.json').write_text(json.dumps({"status":"DIAG_NOT_INTERVAL", "elapsed_seconds":time.monotonic()-start,
                                               "records":records}, indent=2)+'\n')
print(ROOT/'diag_results.json')
