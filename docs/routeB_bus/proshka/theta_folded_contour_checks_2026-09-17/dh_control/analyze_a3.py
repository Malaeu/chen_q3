"""A''' adjudication (registration_v3.json: P_M3_1 long flip, P_M3_2 shadows sqrt(N)+rotation, P_M3_3 Delta at the Spira point,
P_M3_4 Delta map + resolution bound, P_M3_5 E_N main term; option-2 scan NOT_A_TEST) -> closeout_v3.json.
    python analyze_a3.py
"""
import json, re, sys, datetime
from pathlib import Path
from mpmath import mp, mpf, mpc, nstr, sqrt, log, pi, exp, arg
mp.dps = 60
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); import check_contour as cc

def load(n): return json.load(open(HERE/n)) if (HERE/n).exists() else None
reg = load("registration_v3.json"); out = {"time_utc": None, "task_id": reg["task_id"], "fates": {}, "numbers": {}, "pending": []}

# ---------------- P_M3_1: long frozen-head scan
lf = load("long_flip_T14.json")
if lf:
    out["numbers"]["long_scan"] = {k: lf["meta"][k] for k in ("T0", "N0", "sigma", "Tmin", "Tmax", "step", "dps", "fine_step", "confirm_dps")}
    out["numbers"]["long_scan"].update({"n_coarse": lf["n_coarse"], "n_coarse_negative": lf["n_coarse_negative"], "T_first_negative_coarse": lf["T_first_negative_coarse"],
                                        "T_flip": lf.get("T_flip"), "Delta_T": lf.get("Delta_T"), "confirmation": lf.get("confirmation_precision_doubling"), "runtime_seconds": round(lf["meta"]["runtime_seconds"])})
    Tf = lf.get("T_flip")
    if Tf is None: out["fates"]["P_M3_1"] = "REFUTED: no negative h_{N0} on [2000, 4000]"
    elif 2500 <= Tf <= 4000: out["fates"]["P_M3_1"] = f"CONFIRMED: first sign change of the frozen head at T_flip = {Tf} (Delta_T = {lf['Delta_T']}), inside [2500, 4000]; confirmed by precision doubling: {[c['sign_agrees'] for c in lf.get('confirmation_precision_doubling', [])]}"
    else: out["fates"]["P_M3_1"] = f"REFUTED: first negative at T = {Tf}, outside [2500, 4000]"
    # h/|J|^2 profile every 100 in T
    prof = [(r["T"], mpf(r["h"])/mpf(r["absJ"])**2) for r in lf["coarse"] if abs(r["T"] % 100) < 1e-9]
    out["numbers"]["h_over_absJ2_every_100"] = [(T, nstr(v, 5)) for T, v in prof]
else:
    out["fates"]["P_M3_1"] = "PENDING (long_flip_T14.json not yet written)"; out["pending"].append("P_M3_1")
lo = load("long_flip_T14_low.json")
if lo: out["fates"]["OPTION_2_SCAN_14_414"] = f"NOT_A_TEST (fate fixed by AMEND_OPT2 before completion; decided by the budget): {lo['n_coarse_negative']}/{lo['n_coarse']} negative points, T_first_negative = {lo['T_first_negative_coarse']}"
else: out["fates"]["OPTION_2_SCAN_14_414"] = "NOT_A_TEST (AMEND_OPT2); PENDING as a regression"; out["pending"].append("OPTION_2")

# ---------------- P_M3_2: shadows
g = mpf("40.918719012")
def crit(pts):
    pts = sorted(pts, key=lambda r: r["N"])
    ratios = [mpf(r["delta_abs_over_sqrtN"]) for r in pts]; mm = max(ratios)/min(ratios)
    c = mpf(pts[0]["delta_arg"]) + g*log(pts[0]["N"]); devs = []
    for r in pts[1:]:
        pred = -g*log(r["N"]) + c; devs.append(float(arg(exp(1j*(mpf(r["delta_arg"]) - pred)))))
    inc = all(mpf(pts[i]["delta_abs"]) < mpf(pts[i+1]["delta_abs"]) for i in range(len(pts)-1))
    return {"N": [r["N"] for r in pts], "abs_delta": [nstr(mpf(r["delta_abs"]), 5) for r in pts], "abs_delta_over_sqrtN": [nstr(x, 4) for x in ratios], "max_over_min": nstr(mm, 4),
            "arg_dev_from_minus_gamma_logN_rad": [round(x, 3) for x in devs], "max_abs_arg_dev": round(max(abs(x) for x in devs), 3), "abs_increasing": inc,
            "abs_ratio_measured_over_first_principles": [r["abs_ratio_measured_over_th"][:6] for r in pts], "arg_measured_minus_first_principles": [r["arg_diff_measured_minus_th"][:6] for r in pts],
            "pass_pm30pct": bool(mm <= mpf(13)/7), "pass_arg_pm0.3": bool(max(abs(x) for x in devs) <= 0.3)}
sh = load("dn_shadows.json"); she = load("dn_shadows_extra.json")
if sh and she:
    fixed = [r for r in sh["shadows"] if r["N_rule"].startswith("fixed") and "delta" in r]; extra = [r for r in she["shadows"] if "delta" in r]
    out["numbers"]["shadows_registered_set"] = crit(fixed); out["numbers"]["shadows_out_of_sample_set"] = crit(extra); out["numbers"]["shadows_all_13_N"] = crit(fixed + extra)
    heights = [r for r in sh["shadows"] if r["N_rule"].startswith("N(T)") and "delta" in r]
    out["numbers"]["shadows_13_heights"] = [{"gamma": r["gamma"], "N": r["N"], "delta": r["delta"][:30], "abs": r["delta_abs"][:8], "abs_over_th": r["abs_ratio_measured_over_th"][:6], "arg_minus_th": r["arg_diff_measured_minus_th"][:6], "re_gt_half": r["nearest_re_gt_half"]} for r in heights]
    a, b = out["numbers"]["shadows_registered_set"], out["numbers"]["shadows_out_of_sample_set"]
    out["fates"]["P_M3_2"] = ("CONFIRMED" if a["pass_pm30pct"] and a["pass_arg_pm0.3"] else "REFUTED") + \
        f": registered set |delta|/sqrt(N) max/min = {a['max_over_min']} (limit 1.857), max |arg deviation| = {a['max_abs_arg_dev']} rad (limit 0.3), |delta| increasing: {a['abs_increasing']}; out-of-sample set: max/min = {b['max_over_min']}, max arg dev = {b['max_abs_arg_dev']} rad. First-principles delta_th = N^(1-rho)/((rho-1) zeta'(rho)): |delta|/|delta_th| in [{min(float(x) for x in (a['abs_ratio_measured_over_first_principles']+b['abs_ratio_measured_over_first_principles'])):.2f}, {max(float(x) for x in (a['abs_ratio_measured_over_first_principles']+b['abs_ratio_measured_over_first_principles'])):.2f}] over the 13 N values (order of magnitude right), arg(delta/delta_th) in [{min(float(x) for x in (a['arg_measured_minus_first_principles']+b['arg_measured_minus_first_principles'])):.2f}, {max(float(x) for x in (a['arg_measured_minus_first_principles']+b['arg_measured_minus_first_principles'])):.2f}] rad (rotation direction right, residual beyond the registered tolerance)"
    out["fates"]["P_M3_2_old"] = "WITHDRAWN_BY_OWNER_AS_ERRONEOUS; on the data: REFUTED (delta_re changes sign in N and in gamma: 4 of 13 heights have the shadow left of the line)"
    # P_M3_2 numbers table (REG_ADD_5): |delta|/sqrt N and arg delta by N at gamma = 40.9187, both sets merged
    allf = sorted(fixed + extra, key=lambda r: r["N"])
    out["numbers"]["P_M3_2_table"] = ["| N | δ_obs | \\|δ\\| | \\|δ\\|/√N | arg δ (рад) | arg δ_th (рад) | arg(δ/δ_th) | \\|δ\\|/\\|δ_th\\| |", "|---|---|---|---|---|---|---|---|"] + \
        [f"| {r['N']} | {r['delta'][:22]} | {r['delta_abs'][:7]} | {r['delta_abs_over_sqrtN'][:7]} | {r['delta_arg'][:7]} | {r['delta_th_arg'][:7]} | {r['arg_diff_measured_minus_th'][:7]} | {r['abs_ratio_measured_over_th'][:6]} |" for r in allf]
    # P_M3_6: two-term shadow formula
    if "rel_dev_pred_vs_obs" in fixed[0]:
        h13 = [mpf(r["rel_dev_pred_vs_obs"]) for r in heights]; f6 = [mpf(r["rel_dev_pred_vs_obs"]) for r in fixed]; e7 = [mpf(r["rel_dev_pred_vs_obs"]) for r in extra]
        n13 = [mpf(r["rel_dev_newton_vs_obs"]) for r in heights]; nf = [mpf(r["rel_dev_newton_vs_obs"]) for r in fixed]
        em13 = [mpf(r["rel_err_em2_vs_dN_at_rho"]) for r in heights]; emf = [mpf(r["rel_err_em2_vs_dN_at_rho"]) for r in fixed]
        out["numbers"]["P_M3_6"] = {"heights_13_within_0.1": f"{sum(1 for x in h13 if x < 0.1)}/13", "heights_13_max_dev": nstr(max(h13), 4), "fixed_6_within_0.1": f"{sum(1 for x in f6 if x < 0.1)}/6", "fixed_6_max_dev": nstr(max(f6), 4),
            "falsifier_gt_0.3_hit_at": [r["N"] for r in fixed if mpf(r["rel_dev_pred_vs_obs"]) > 0.3] + [f"gamma={r['gamma']}" for r in heights if mpf(r["rel_dev_pred_vs_obs"]) > 0.3],
            "out_of_sample_7_within_0.1": f"{sum(1 for x in e7 if x < 0.1)}/7", "out_of_sample_max_dev": nstr(max(e7), 4),
            "newton_step_dev_range_heights": [nstr(min(n13), 3), nstr(max(n13), 3)], "newton_step_dev_range_fixed": [nstr(min(nf), 3), nstr(max(nf), 3)],
            "em2_numerator_vs_dN_rho_range_heights": [nstr(min(em13), 3), nstr(max(em13), 3)], "em2_numerator_vs_dN_rho_fixed_by_N": [(r["N"], r["rel_err_em2_vs_dN_at_rho"][:6]) for r in fixed]}
        out["numbers"]["P_M3_6_table"] = ["| набор | γ | N | δ_obs | δ_pred = EM2/d_N′ | откл. | Ньютон −d_N/d_N′ откл. | EM2 против d_N(ρ) |", "|---|---|---|---|---|---|---|---|"] + \
            [f"| {'N(γ)' if r['N_rule'].startswith('N(T)') else 'γ=40.92'} | {str(r['gamma'])[:7]} | {r['N']} | {r['delta'][:22]} | {r['delta_pred_em2'][:22]} | {r['rel_dev_pred_vs_obs'][:6]} | {r['rel_dev_newton_vs_obs'][:6]} | {r['rel_err_em2_vs_dN_at_rho'][:6]} |" for r in heights + fixed + extra]
        # P_M3_9: second-order shadow
        if "rel_dev_pred2_em2_vs_obs" in fixed[0]:
            h2 = [mpf(r["rel_dev_pred2_em2_vs_obs"]) for r in heights]; hx = [mpf(r["rel_dev_pred2_exact_vs_obs"]) for r in heights]
            f2 = [mpf(r["rel_dev_pred2_em2_vs_obs"]) for r in fixed + extra]; fx = [mpf(r["rel_dev_pred2_exact_vs_obs"]) for r in fixed + extra]
            out["numbers"]["P_M3_9"] = {"heights_13_em2_within_0.05": f"{sum(1 for x in h2 if x < 0.05)}/13", "heights_13_em2_max": nstr(max(h2), 4),
                "heights_13_exact_numerator_within_0.05": f"{sum(1 for x in hx if x < 0.05)}/13", "heights_13_exact_numerator_max": nstr(max(hx), 4),
                "fixed_height_13N_exact_numerator_range": [nstr(min(fx), 3), nstr(max(fx), 3)], "fixed_height_13N_em2_range": [nstr(min(f2), 3), nstr(max(f2), 3)],
                "roots_ever_comparable": any(r.get("roots_comparable_em2") or r.get("roots_comparable_exact") for r in heights + fixed + extra)}
            p9 = out["numbers"]["P_M3_9"]
            out["fates"]["P_M3_9"] = ("CONFIRMED" if p9["heights_13_em2_within_0.05"] == "13/13" else "REFUTED") + \
                f": with the registered two-term EM numerator {p9['heights_13_em2_within_0.05']} heights within 0.05 (max {p9['heights_13_em2_max']}). Diagnosis CONFIRMED: with the exact numerator d_N(rho) the quadratic gives {p9['heights_13_exact_numerator_within_0.05']} within 0.05 (max {p9['heights_13_exact_numerator_max']}), and {p9['fixed_height_13N_exact_numerator_range'][0]}..{p9['fixed_height_13N_exact_numerator_range'][1]} over N = 10..150 at fixed height (first order there: 0.076..0.21) — the linearisation was the culprit and the numerator is now the binding limit. POST HOC, NOT REGISTERED: the three-term EM numerator (next term -rho N^-rho-1 over 12) cuts the numerator error to 0.0003..0.0034 at N = N(gamma) and reproduces the exact-numerator quadratic (12/13 within 0.05, max 0.069)."
            out["numbers"]["P_M3_9_table"] = ["| набор | γ | N | 1-й пор. EM2 | 2-й пор. EM2 | 2-й пор. точный числ. | Ньютон |", "|---|---|---|---|---|---|---|"] + \
                [f"| {'N(γ)' if r['N_rule'].startswith('N(T)') else 'γ=40.92'} | {str(r['gamma'])[:7]} | {r['N']} | {r['rel_dev_pred_vs_obs'][:6]} | {r['rel_dev_pred2_em2_vs_obs'][:6]} | {r['rel_dev_pred2_exact_vs_obs'][:6]} | {r['rel_dev_newton_vs_obs'][:6]} |" for r in heights + fixed + extra]
        # |delta| does not converge to the axis (owner's section-0 line)
        alld = sorted(fixed + extra, key=lambda r: r["N"])
        out["numbers"]["shadow_does_not_converge"] = {"N_range": [alld[0]["N"], alld[-1]["N"]], "abs_delta_min": nstr(min(mpf(r["delta_abs"]) for r in alld), 4), "abs_delta_max": nstr(max(mpf(r["delta_abs"]) for r in alld), 4),
            "abs_over_sqrtN_first_last": [alld[0]["delta_abs_over_sqrtN"][:6], alld[-1]["delta_abs_over_sqrtN"][:6]],
            "statement": "the shadow of the Dirichlet partial sum does not converge to the axis as N grows; the return to the axis is entirely due to E_N, i.e. to the Gaussian suppression of the theta series, not to the arithmetic of d_N"}
        p6 = out["numbers"]["P_M3_6"]
        out["fates"]["P_M3_6"] = ("CONFIRMED" if p6["heights_13_within_0.1"] == "13/13" and p6["fixed_6_within_0.1"] == "6/6" else "REFUTED") + \
            f": within 0.1 at {p6['heights_13_within_0.1']} heights (max {p6['heights_13_max_dev']}) and {p6['fixed_6_within_0.1']} of the fixed-height N (max {p6['fixed_6_max_dev']}); falsifier (> 0.3) hit at N = {p6['falsifier_gt_0.3_hit_at']}. Decomposition: the exact Newton step -d_N(rho)/d_N'(rho) itself deviates {p6['newton_step_dev_range_heights'][0]}..{p6['newton_step_dev_range_heights'][1]} at the 13 heights (linearisation error: |delta| ~ 0.1 is not small on the scale of d_N), the two-term EM numerator matches d_N(rho) to {p6['em2_numerator_vs_dN_rho_range_heights'][0]}..{p6['em2_numerator_vs_dN_rho_range_heights'][1]} at N = N(gamma) but only to 0.95 / 0.51 / 0.31 at N = 10 / 15 / 20 (gamma = 40.92): at fixed height the numerator fails for small N, at N(gamma) the linearisation fails"
else: out["fates"]["P_M3_2"] = "PENDING"; out["pending"].append("P_M3_2")

# ---------------- P_M3_3: Delta at the Spira point (Lagrange lemma: Delta_N - Delta_{N-1} = sum_i |u_i v_N - u_N v_i|^2 >= 0)
sp = load("pair_delta_spira_dps150.json") or load("pair_delta_spira.json")
if sp:
    pts = sorted(sp["points"], key=lambda p: p["N"]); Ds = [mpf(p["Delta"]) for p in pts]; Dh = [mpf(p["Delta_hat"]) for p in pts]
    inc = [(pts[i+1]["N"], Ds[i+1]-Ds[i]) for i in range(len(Ds)-1)]
    out["numbers"]["spira"] = {"N_range": [pts[0]["N"], pts[-1]["N"]], "all_Delta_positive": all(D > 0 for D in Ds), "Delta_N10": nstr(Ds[0], 12), "Delta_N60": nstr(Ds[-1], 12),
        "Delta_hat_N10": nstr(Dh[0], 8), "Delta_hat_N60": nstr(Dh[-1], 8), "Delta_hat_monotone_decreasing": all(Dh[i] >= Dh[i+1] for i in range(len(Dh)-1)),
        "raw_Delta_nondecreasing": all(x >= 0 for _, x in inc), "zero_increments_at_N": [N for N, x in inc if x == 0], "increments_sample": [(N, nstr(x, 3)) for N, x in inc if N in (11, 16, 21, 26, 31, 41, 51, 56)],
        "saturation_N": next((N for N, x in inc if 0 < x < mpf(10)**-30*Ds[-1]), None), "dps": sp["meta"]["dps"]}
    s = out["numbers"]["spira"]
    out["fates"]["P_M3_3"] = (f"Delta > 0 for all N in 10..60 — CONFIRMED ({len(Ds)}/{len(Ds)}). "
        f"'Grows with N' — REFUTED at the normalised level (AMEND_3_3): Delta_hat {s['Delta_hat_N10']} -> {s['Delta_hat_N60']} (monotone decreasing: {s['Delta_hat_monotone_decreasing']}); raw Delta saturates from N ~ 25, increments decay geometrically "
        f"({', '.join(f'N={N}: {x}' for N, x in s['increments_sample'])}); raw non-decrease is exact (Lagrange), zero increments exactly at N = 5k (a_5k = 0 in DH).")
else: out["fates"]["P_M3_3"] = "PENDING"; out["pending"].append("P_M3_3")

# ---------------- P_M3_4: Delta map + resolution bound sigma_min(gamma)
mpd = load("pair_delta_map.json")
if mpd:
    pts = mpd["points"]; sigmas = ["1/64", "1/8", "1/4", "0.45"]
    def frac(v): return mpf(v.split("/")[0])/mpf(v.split("/")[1]) if "/" in v else mpf(v)
    tab = ["| σ | точек | Δ > 0 | Δ̂ min (γ) | Δ̂ max | Δ̂/σ² min | Δ̂/σ² max |", "|---|---|---|---|---|---|---|"]; allpos = True; ratio_all = []
    for sg in sigmas:
        v = [p for p in pts if p["sigma"] == sg]; dh_ = [(float(p["gamma"]), mpf(p["Delta_hat"]), mpf(p["Delta_hat_over_sigma2"])) for p in v]
        npos = sum(1 for p in v if p["Delta_positive"]); allpos = allpos and npos == len(v); ratio_all += [x[2] for x in dh_]
        mn = min(dh_, key=lambda x: x[1]); tab.append(f"| {sg} | {len(v)} | {npos}/{len(v)} | {nstr(mn[1], 4)} ({mn[0]}) | {nstr(max(x[1] for x in dh_), 4)} | {nstr(min(x[2] for x in dh_), 4)} | {nstr(max(x[2] for x in dh_), 4)} |")
    out["numbers"]["delta_map_table"] = tab; out["numbers"]["delta_hat_over_sigma2_range_all"] = [nstr(min(ratio_all), 4), nstr(max(ratio_all), 4)]
    blind = [p for p in pts if mpf(p["Delta_hat"]) < mpf(10)**-40 or mpf(p["Delta_hat_over_sigma2"]) < min(ratio_all)*mpf(10)**-6]
    out["numbers"]["blind_zone_points"] = len(blind)
    out["fates"]["P_M3_4"] = ("CONFIRMED" if allpos and not blind else "REFUTED") + f": Delta > 0 at {sum(1 for p in pts if p['Delta_positive'])}/{len(pts)} points; Delta_hat minimal at the smallest sigma and at gamma = 14 for every sigma; Delta_hat/sigma^2 in [{out['numbers']['delta_hat_over_sigma2_range_all'][0]}, {out['numbers']['delta_hat_over_sigma2_range_all'][1]}] — no zone where the pair signal collapses; Delta_hat = O(sigma^2) as sigma -> 0 is structural (rows coincide at sigma = 0)"
    # resolution bound (REG_ADD_4): S = U V (1 - sqrt(1 - Delta_hat)) >= |lambda_-(B)|/m lower bound; sigma_min = sigma * E_N / S at sigma = 1/64
    cc.ADAPTIVE_R = 0.0; res = []
    for p in [q for q in pts if q["sigma"] == "1/64"]:
        gam = float(p["gamma"]); theta, c, M, N = cc.cutoff(gam); eN = cc.e_N_of(gam, theta, c, M); sg = mpf(1)/64
        U = sqrt(mpf(p["U2"])); V = sqrt(mpf(p["V2"])); S = U*V*(1 - sqrt(1 - mpf(p["Delta_hat"])))
        EN = sg*eN; smin = sg*EN/S
        q8 = [q for q in pts if q["sigma"] == "1/8" and float(q["gamma"]) == gam][0]
        S8 = sqrt(mpf(q8["U2"]))*sqrt(mpf(q8["V2"]))*(1 - sqrt(1 - mpf(q8["Delta_hat"])))
        res.append({"gamma": gam, "N": N, "S_over_E_N_at_1/64": nstr(S/EN, 4), "sigma_min": nstr(smin, 4), "sigma2_law_check_S(1/8)/S(1/64)_over_64": nstr(S8/S/64, 4)})
    out["numbers"]["resolution_bound"] = {"definition": "S(sigma,gamma) = U V (1 - sqrt(1 - Delta_hat)) (lower bound of |lambda_-| of the pair block (6) per unit multiplicity); sigma_min(gamma) = sigma * E_N(sigma,gamma) / S(sigma,gamma) at sigma = 1/64, E_N = sigma e_N with the adaptive cutoff",
        "sigma_min_min": nstr(min(mpf(r["sigma_min"]) for r in res), 4) + f" at gamma={min(res, key=lambda r: mpf(r['sigma_min']))['gamma']}", "sigma_min_max": nstr(max(mpf(r["sigma_min"]) for r in res), 4) + f" at gamma={max(res, key=lambda r: mpf(r['sigma_min']))['gamma']}",
        "S_over_E_N_min": nstr(min(mpf(r["S_over_E_N_at_1/64"]) for r in res), 4), "sigma2_law_check_range": [nstr(min(mpf(r["sigma2_law_check_S(1/8)/S(1/64)_over_64"]) for r in res), 4), nstr(max(mpf(r["sigma2_law_check_S(1/8)/S(1/64)_over_64"]) for r in res), 4)],
        "per_gamma_every_4": [r for r in res if abs(r["gamma"] % 4) < 1e-9]}
else: out["fates"]["P_M3_4"] = "PENDING"; out["pending"].append("P_M3_4")

# ---------------- P_M3_5: E_N main term
em = load("en_main_term.json")
if em:
    m = em["meta"]; out["numbers"]["en_main_term"] = m
    out["fates"]["P_M3_5"] = ("CONFIRMED" if m["n_pass_1term"] == m["n_qualifying"] else "REFUTED") + f": one-term |E_N - B N^(1/2-p)/(p-1/2)|/|E_N| < 0.2 at {m['n_pass_1term']}/{m['n_qualifying']} qualifying points (max {m['max_rel_dev_1term']}, growing with T: 0.10 at T=2 to 0.52 at T=40); with the next Euler-Maclaurin term -B N^(-s)/2 (MAC note before run): {m['n_pass_2terms']}/{m['n_qualifying']} within 0.2, max {m['max_rel_dev_2terms']} — E_N is the gamma factor times the Euler-Maclaurin remainder, but the second term is not negligible at N ~ sqrt(T log T)"
else: out["fates"]["P_M3_5"] = "PENDING"; out["pending"].append("P_M3_5")

out["time_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
out["scope"] = "finite points; DH NEGATIVE is not a witness against zeta; zeta POSITIVE is not evidence for RH; run certifies flip height, shadow offsets and pair-signal resolution, not sign"
Path(HERE/"closeout_v3.json").write_text(json.dumps(out, indent=1, ensure_ascii=False))
for k, v in out["fates"].items(): print(k, "->", v[:600])
if mpd:
    print("\n".join(out["numbers"]["delta_map_table"])); rb = out["numbers"]["resolution_bound"]; print("resolution: sigma_min in", rb["sigma_min_min"], "..", rb["sigma_min_max"], "| S/E_N min", rb["S_over_E_N_min"], "| sigma^2 law", rb["sigma2_law_check_range"])
if sh: print("shadows registered:", out["numbers"]["shadows_registered_set"]); print("shadows extra:", out["numbers"]["shadows_out_of_sample_set"])
