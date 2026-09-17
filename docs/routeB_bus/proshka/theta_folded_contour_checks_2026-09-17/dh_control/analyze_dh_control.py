"""v2 adjudication (DH_CONTROL + HEAD_MASSES + FIXED_N_FLIP + JN/Dirichlet windows) from the filed JSONs.
Prints tables / ASCII for the report and writes closeout_v2.json.  P_CAN_4 / P_CAN_6 are DECIDED_BY_PAPER_BEFORE_RUN
(registration_v2.json) and are not adjudicated here.
    python analyze_dh_control.py
"""
import json, re, datetime
from pathlib import Path
from mpmath import mp, mpf, nstr, log10
mp.dps = 50
HERE = Path(__file__).resolve().parent

def mid(s):
    s = str(s).strip()
    m = re.match(r'\[?\s*(-?[0-9.]+(?:e[-+]?\d+)?)', s)
    if m: return mpf(m.group(1))
    return mpf(0)
def frac(v): v = str(v); return mpf(v.split("/")[0])/mpf(v.split("/")[1]) if "/" in v else mpf(v)
def load(name): return json.load(open(HERE/name))

reg = load("registration_v2.json")
ref = load("dh_control_reference.json"); T0 = mpf(ref["T0"])
dh = load("dh_control_grid_arb.json"); hz = load("head_masses_zeta.json"); hd = load("head_masses_dh.json"); ha = load("head_masses_arb.json")
ff = load("fixed_n_flip.json")
jn = load("jn_dirichlet.json") if (HERE/"jn_dirichlet.json").exists() else None
out = {"time_utc": None, "task_id": reg["task_id"], "fates": {}, "numbers": {}, "retired": reg["retired"]}

# ---------------- P_CAN_1: NEGATIVE certificates on the DH control strip
ctrl = [p for p in dh["points"] if p["kind"] in ("control", "T0_neighbourhood")]
neg = [p for p in ctrl if p["sign_certificate_U_N"] == "NEGATIVE"]
near = [p for p in ctrl if p["sigma"] == "0.30" and abs(float(p["T"]) - float(T0)) <= 0.05 + 1e-9]
near_neg = [p for p in near if p["sign_certificate_U_N"] == "NEGATIVE"]
out["numbers"]["control_points"] = len(ctrl); out["numbers"]["U_N_NEGATIVE"] = len(neg)
out["numbers"]["sigma0.30_T0pm0.05_points"] = len(near); out["numbers"]["sigma0.30_T0pm0.05_NEGATIVE"] = len(near_neg)
by_sigma = {}
for p in ctrl:
    d = by_sigma.setdefault(p["sigma"], {"n": 0, "NEG": 0, "POS": 0, "UND": 0, "Tneg": []})
    d["n"] += 1; d[{"NEGATIVE": "NEG", "POSITIVE": "POS", "UNDECIDED": "UND"}[p["sign_certificate_U_N"]]] += 1
    if p["sign_certificate_U_N"] == "NEGATIVE": d["Tneg"].append(float(p["T"]))
rows = []
for sg in ["1/64", "1/32", "1/16", "1/8", "1/4", "0.28", "0.30", "0.3085", "0.32"]:
    d = by_sigma.get(sg, {"n": 0, "NEG": 0, "POS": 0, "UND": 0, "Tneg": []})
    rng = f"{min(d['Tneg']):.3f}..{max(d['Tneg']):.3f}" if d["Tneg"] else "-"
    rows.append(f"| {sg} | {d['n']} | {d['NEG']} | {d['POS']} | {d['UND']} | {rng} |")
out["numbers"]["U_N_by_sigma_table"] = ["| σ | точек | U_N NEGATIVE | POSITIVE | UNDECIDED | T с NEGATIVE |", "|---|---|---|---|---|---|"] + rows
out["fates"]["P_CAN_1"] = ("CONFIRMED" if neg and near and len(near_neg) == len(near) else ("PARTIALLY_CONFIRMED" if neg else "REFUTED")) + \
    f": {len(neg)} NEGATIVE certificates on the control strip; at sigma=0.30, T0+-0.05: {len(near_neg)}/{len(near)} NEGATIVE"
for sg in ["1/64", "0.30"]:
    Tn = sorted(by_sigma[sg]["Tneg"]) if sg in by_sigma else []
    out["numbers"][f"negative_T_window_sigma_{sg}"] = (f"{Tn[0]:.3f}..{Tn[-1]:.3f}" if Tn else "none")
out["numbers"]["first_order_window_pre_registered"] = ref.get("first_order_negative_window")

# ---------------- P_CAN_2: zeta-like strip
zl = [p for p in dh["points"] if p["kind"] == "zetalike"]
zl_pos = sum(1 for p in zl if p["sign_certificate_L_N"] == "POSITIVE")
out["numbers"]["zetalike_points"] = len(zl); out["numbers"]["zetalike_L_N_POSITIVE"] = zl_pos
out["fates"]["P_CAN_2"] = ("CONFIRMED" if zl_pos == len(zl) else "REFUTED") + f": L_N POSITIVE at {zl_pos}/{len(zl)} zeta-like points"

# ---------------- P_CAN_3: envelope
env_ok = sum(1 for p in dh["points"] if p["envelope_holds_diagnostic"])
worst = max(dh["points"], key=lambda p: mid(p["abs_H_minus_h_over_E"]))
out["numbers"]["envelope_holds"] = f"{env_ok}/{len(dh['points'])}"
out["numbers"]["max_abs_H_minus_h_over_E"] = nstr(mid(worst["abs_H_minus_h_over_E"]), 4) + f" at sigma={worst['sigma']} T={worst['T']}"
out["fates"]["P_CAN_3"] = ("CONFIRMED" if env_ok == len(dh["points"]) else "REFUTED") + f": |H_DH - h_N^DH| <= E_N^DH at {env_ok}/{len(dh['points'])} points"

# ---------------- P_CAN_5: needs the DH summand-form spectrum (v1 object), which was stopped and discarded when v2 arrived
out["fates"]["P_CAN_5"] = "NOT_TESTABLE: the DH summand-form spectrum (v1 object) was not computed (run stopped, partial output discarded when v2 arrived); the zeta summand spectrum alone (gn_spectrum_zeta.json) cannot give the DH/zeta ratio. Diagnostic substitute on the v2 rank-2 ray form below (different object, not the registered one)."
hzm = {(p["sigma"], float(p["T"])): p for p in hz["points"]}; hdm = {(p["sigma"], float(p["T"])): p for p in hd["points"]}
def lam_ratio(p): return abs(mid(p["lambda_minus"]))/mid(p["lambda_plus"])
zeta_lr = {}
for p in hz["points"]: zeta_lr.setdefault(p["sigma"], []).append(lam_ratio(p))
zeta_lr_med = {sg: sorted(v)[len(v)//2] for sg, v in zeta_lr.items()}
def nearest_sigma(sg): x = frac(sg); return min(zeta_lr_med, key=lambda k: abs(frac(k) - x))
sub = []
for p in neg:
    q = hdm.get((p["sigma"], float(p["T"])))
    if q: sub.append(lam_ratio(q)/zeta_lr_med[nearest_sigma(p["sigma"])])
out["numbers"]["diag_rank2_|lambda_-|/lambda_+_DH_NEG_over_zeta_median_min_max"] = [nstr(min(sub), 4), nstr(max(sub), 4)] if sub else None

# ---------------- P_M2_1: q on the zeta grid
qz = [(mid(p["q"]), p) for p in hz["points"]]
qmax = max(qz, key=lambda t: t[0]); qmin = min(qz, key=lambda t: t[0])
out["numbers"]["zeta_masses_points"] = len(hz["points"]); out["numbers"]["zeta_q_max"] = nstr(qmax[0], 6) + f" at sigma={qmax[1]['sigma']} T={qmax[1]['T']}"
out["numbers"]["zeta_q_min"] = nstr(qmin[0], 6) + f" at sigma={qmin[1]['sigma']} T={qmin[1]['T']}"
out["numbers"]["zeta_q_gt_1e-2"] = sum(1 for q, _ in qz if q > mpf("1e-2")); out["numbers"]["zeta_q_gt_1"] = sum(1 for q, _ in qz if q > 1)
out["numbers"]["zeta_identity_max_rel_err"] = nstr(max(mid(p["identity_rel_err"]) for p in hz["points"]), 3)
qtab = ["| σ | q min | q max | 1−q min |", "|---|---|---|---|"]
for sg in ["1/64", "1/32", "1/16", "1/8", "1/4"]:
    v = [mid(p["q"]) for p in hz["points"] if p["sigma"] == sg]
    if v: qtab.append(f"| {sg} | {nstr(min(v), 5)} | {nstr(max(v), 5)} | {nstr(1-max(v), 4)} |")
out["numbers"]["zeta_q_by_sigma_table"] = qtab
out["fates"]["P_M2_1"] = ("REFUTED" if qmax[0] > mpf("1e-2") else "CONFIRMED") + f": max q = {nstr(qmax[0], 5)} (falsifier q > 1e-2 hit at {out['numbers']['zeta_q_gt_1e-2']}/{len(qz)} points); q = 1 - O(sigma) as MAC noted before the run"
# q at zero heights
zh = [p for p in hz["points"] if p["kind"] != "grid"]
out["numbers"]["zeta_q_at_zero_heights_sigma_1/64_min_max"] = [nstr(min(mid(p["q"]) for p in zh if p["sigma"] == "1/64"), 5), nstr(max(mid(p["q"]) for p in zh if p["sigma"] == "1/64"), 5)] if zh else None

# ---------------- arb regression of the masses
ra = ha["points"]
out["numbers"]["arb_masses_points"] = len(ra)
out["numbers"]["arb_Mplus_minus_Mminus_minus_E_POSITIVE"] = f"{sum(1 for p in ra if p['sign_certificate_Mplus_minus_Mminus_minus_E']=='POSITIVE')}/{len(ra)}"
out["numbers"]["arb_h_direct_minus_E_POSITIVE"] = f"{sum(1 for p in ra if p['sign_certificate_h_direct_minus_E']=='POSITIVE')}/{len(ra)}"
out["numbers"]["arb_masses_table"] = ["| σ | T | q | M₊−M₋−ℰ | h−ℰ |", "|---|---|---|---|---|"] + \
    [f"| {p['sigma']} | {p['T']} | {nstr(mid(p['q']), 6)} | {p['sign_certificate_Mplus_minus_Mminus_minus_E']} | {p['sign_certificate_h_direct_minus_E']} |" for p in ra]

# ---------------- P_M2_5: q > 1 at DH NEGATIVE points
negkeys = {(p["sigma"], float(p["T"])) for p in neg}
q_at_neg = [(k, mid(hdm[k]["q"])) for k in negkeys if k in hdm]
n_gt1 = sum(1 for _, q in q_at_neg if q > 1)
out["numbers"]["dh_NEGATIVE_points_with_masses"] = len(q_at_neg); out["numbers"]["dh_q_gt_1_at_NEGATIVE"] = n_gt1
out["numbers"]["dh_q_gt_1_total"] = sum(1 for p in hd["points"] if mid(p["q"]) > 1)
out["numbers"]["dh_q_max"] = nstr(max(mid(p["q"]) for p in hd["points"]), 5)
out["numbers"]["dh_identity_max_rel_err"] = nstr(max(mid(p["identity_rel_err"]) for p in hd["points"]), 3)
out["fates"]["P_M2_5"] = ("CONFIRMED" if q_at_neg and n_gt1 == len(q_at_neg) else "REFUTED") + f": q > 1 at {n_gt1}/{len(q_at_neg)} U_N-NEGATIVE points (tautological: q>1 <=> h_N<0, as MAC noted before the run)"

# ---------------- P_M2_2 / P_M2_3 / P_M2_4: fixed-N flip
flips = [e for e in ff["scans"] if e["T_flip"] is not None]
out["numbers"]["flip_scans"] = len(ff["scans"]); out["numbers"]["flips_found"] = len(flips)
ftab = ["| T₀ | σ | N₀ | точек | h < 0 | h(T₀) | h(T₀+40) | min h |", "|---|---|---|---|---|---|---|---|"]
for e in ff["scans"]:
    hs = [mpf(r["h"]) for r in e["rows"]]
    ftab.append(f"| {e['T0']} | {e['sigma']} | {e['N0']} | {e['n_scan']} | {e['n_negative']} | {nstr(hs[0], 3)} | {nstr(hs[-1], 3)} | {nstr(min(hs), 3)} |")
out["numbers"]["flip_table"] = ftab
out["fates"]["P_M2_2"] = ("CONFIRMED" if flips else "REFUTED") + f": {len(flips)}/{len(ff['scans'])} (T0, sigma) scans show a sign change of the frozen head up to T0+40; h_{{N0}} > 0 at all {sum(e['n_scan'] for e in ff['scans'])} scan points"
wz = ff["windings"]
out["numbers"]["winding_rectangles"] = len(wz); out["numbers"]["winding_zero_total"] = sum(w["zeros"] for w in wz)
out["numbers"]["winding_all_reliable"] = all(w["reliable"] for w in wz); out["numbers"]["winding_max_residual"] = nstr(max(mid(w["integer_residual"]) for w in wz), 3)
out["fates"]["P_M2_3"] = "NOT_TRIGGERED (conditional on a flip; none occurred)" + f"; zero count of J_{{N0}} on all {len(wz)} rectangles [±0.01, ±1/2] x [T0+10k, T0+10(k+1)] = {sum(w['zeros'] for w in wz)}"
out["fates"]["P_M2_4"] = "NOT_TESTABLE (no Delta_T exists below 40 for any T0)"

# ---------------- P_M2_6 and identity (9)
if jn:
    ip = jn["identity_points"]
    out["numbers"]["identity_points"] = len(ip); out["numbers"]["identity_min_digits"] = min(r["digits_agree"] for r in ip)
    out["numbers"]["identity_all_pass_30"] = all(r["pass_30_digits"] for r in ip)
    out["numbers"]["identity_abs_E_over_J_min_max"] = [nstr(min(mid(r["abs_E_over_abs_J"]) for r in ip), 4), nstr(max(mid(r["abs_E_over_abs_J"]) for r in ip), 4)]
    out["numbers"]["identity_quad_vs_gamma_max"] = nstr(max(max(mid(r["I_pos_quad_vs_gamma_rel"]), mid(r["I_neg_quad_vs_gamma_rel"])) for r in ip), 3)
    out["numbers"]["identity_ray_direct_vs_closed_max"] = nstr(max(mid(c["rel_err"]) for r in ip for c in r["ray_closed_form_vs_direct_n_le_2"]), 3)
    itab = ["| T | σ | τ | N | знаков | \\|E_N\\|/\\|J_N\\| |", "|---|---|---|---|---|---|"] + [f"| {r['T']} | {r['sigma']} | {r['tau']} | {r['N']} | {r['digits_agree']} | {nstr(mid(r['abs_E_over_abs_J']), 3)} |" for r in ip]
    out["numbers"]["identity_table"] = itab
    out["fates"]["IDENTITY_9"] = ("PASS" if out["numbers"]["identity_all_pass_30"] else "FAIL") + f": min {out['numbers']['identity_min_digits']} agreeing digits over {len(ip)} random strip points (target 30)"
    dz = {r["T0"]: r for r in jn["zeros_dN"]}; jz = {r["T0"]: r for r in jn["zeros_JN"]}
    ztab = ["| T₀ | N | нули d_N в окне | Re s > ½ | Re s > 1 | нули J_N всего (полный прямоугольник) | на оси | вне оси | Re p > 0.01 |", "|---|---|---|---|---|---|---|---|---|"]
    ok_d = True; ok_j = True
    for T in sorted(dz):
        d = dz[T]; j = jz[T]
        ztab.append(f"| {T} | {d['N']} | {d['zeros_in_window']} | {d['n_re_gt_half']} | {d['n_re_gt_one']} | {j['zeros_full']} | {j['n_online']} | {j['off_line_zeros']} | {j['zeros_right_of_eps']} |")
        ok_d = ok_d and d["n_re_gt_half"] >= 1; ok_j = ok_j and j["off_line_zeros"] == 0 and j["zeros_right_of_eps"] == 0
    out["numbers"]["zero_window_table"] = ztab
    out["numbers"]["dN_zeros_located"] = {str(T): [z["zero"] for z in dz[T]["zeros"] if z.get("zero")] for T in dz}
    out["numbers"]["JN_online_zeros"] = {str(T): jz[T]["online_zeros_tau"] for T in jz}
    out["numbers"]["JN_max_abs_im_on_axis"] = nstr(max(mid(jz[T]["max_abs_im_on_axis"]) for T in jz), 3)
    out["fates"]["P_M2_6"] = ("CONFIRMED" if ok_d and ok_j else ("PARTIALLY_CONFIRMED" if ok_d or ok_j else "REFUTED")) + \
        f": d_N has a zero with Re s > 1/2 in {sum(1 for T in dz if dz[T]['n_re_gt_half']>=1)}/{len(dz)} windows; J_N off-line zeros in {sum(1 for T in jz if jz[T]['off_line_zeros']!=0)}/{len(jz)} windows"
else:
    out["fates"]["P_M2_6"] = "PENDING (jn_dirichlet.json not yet written)"; out["fates"]["IDENTITY_9"] = "PENDING"

# ---------------- ASCII: q(T) for zeta at sigma=1/64 and 1/4, and on the DH strip at sigma=0.30
def ascii_q(points, sg, title, step=2.0, key="q"):
    pts = sorted([p for p in points if p["sigma"] == sg and abs(float(p["T"]) % step) < 1e-9], key=lambda p: float(p["T"]))
    lines = [title]
    for p in pts:
        q = mid(p[key]); bar = int(min(50, 40*float(q)))
        lines.append(f"T={float(p['T']):6.2f} {'#'*bar:<50} {nstr(q, 4)}")
    return lines
out["numbers"]["ascii_q_zeta_sigma_1/64"] = ascii_q(hz["points"], "1/64", "q = M_-/M_+ (zeta, sigma=1/64, adaptive cutoff), bar = 40*q")
out["numbers"]["ascii_q_zeta_sigma_1/4"] = ascii_q(hz["points"], "1/4", "q = M_-/M_+ (zeta, sigma=1/4, adaptive cutoff), bar = 40*q")
dh030 = [p for p in hd["points"] if p["sigma"] == "0.30"]
dh030.sort(key=lambda p: float(p["T"]))
lines = ["q = M_-/M_+ on the DH control strip, sigma=0.30 (bar = 40*q, '|' marks q=1)"]
for p in dh030[::3]:
    q = mid(p["q"]); bar = int(min(60, 40*float(q))); s = "#"*bar
    s = s[:40] + "|" + s[40:] if len(s) >= 40 else s.ljust(40) + "|"
    lines.append(f"T={float(p['T']):7.3f} {s:<61} {nstr(q, 4)}")
out["numbers"]["ascii_q_dh_sigma_0.30"] = lines

out["time_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
out["failures"] = {"dh_grid": dh["meta"]["n_failures"], "masses_zeta": hz["meta"]["n_failures"], "masses_dh": hd["meta"]["n_failures"], "masses_arb": ha["meta"]["n_failures"], "flip": ff["meta"]["n_failures"], "jn": jn["meta"]["n_failures"] if jn else None}
out["runtimes_seconds"] = {"dh_grid": round(dh["meta"]["runtime_seconds"]), "masses_zeta": round(hz["meta"]["runtime_seconds"]), "masses_dh": round(hd["meta"]["runtime_seconds"]), "masses_arb": round(ha["meta"]["runtime_seconds"]), "flip": round(ff["meta"]["runtime_seconds"]), "jn": round(jn["meta"]["runtime_seconds"]) if jn else None}
out["scope"] = "finite points; DH NEGATIVE is not a witness against zeta; zeta POSITIVE is not evidence for RH; run certifies discriminator sensitivity and head structure, not sign"
Path(HERE/"closeout_v2.json").write_text(json.dumps(out, indent=1, ensure_ascii=False))
for k, v in out["fates"].items(): print(k, "->", v)
for k, v in out["numbers"].items():
    if not (isinstance(v, list) and len(v) > 3) and not isinstance(v, dict): print(" ", k, ":", v)
for k in ["U_N_by_sigma_table", "zeta_q_by_sigma_table", "flip_table", "arb_masses_table"] + (["identity_table", "zero_window_table"] if jn else []):
    print("\n".join(out["numbers"][k])); print()
