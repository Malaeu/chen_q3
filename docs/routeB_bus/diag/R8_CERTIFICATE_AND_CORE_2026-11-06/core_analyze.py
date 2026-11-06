#!/usr/bin/env python3
"""Summarize the completed Round 8 core scan and emit dependency-free SVG plots."""
from __future__ import annotations

import csv
import gzip
import json
import math
import platform
import re
import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent


def rows_csv(path: Path):
    with path.open(newline="", encoding="utf-8") as f:
        yield from csv.DictReader(f)


def safe_range(values):
    xs = [float(x) for x in values if x is not None and math.isfinite(float(x))]
    return (min(xs), max(xs)) if xs else (None, None)


def log_slope(rows, ykey):
    pts = [(math.log(float(r["N"])), math.log(float(r[ykey])))
           for r in rows if float(r[ykey]) > 0 and float(r["N"]) > 0]
    mx = sum(x for x, _ in pts) / len(pts)
    my = sum(y for _, y in pts) / len(pts)
    den = sum((x - mx) ** 2 for x, _ in pts)
    return sum((x - mx) * (y - my) for x, y in pts) / den


def decade_bounds(n: int):
    if n < 10:
        return 3, 9
    p = 10 ** int(math.log10(n))
    return p, min(10 * p - 1, 10_000_000)


def svg_plot(path: Path, title: str, xlabel: str, ylabel: str,
             series: list[tuple[str, list[tuple[float, float]], str]],
             marks: list[tuple[float, float]] | None = None,
             note: str | None = None):
    marks = marks or []
    all_points = [p for _, pts, _ in series for p in pts if p[0] > 0 and p[1] > 0]
    all_points += [p for p in marks if p[0] > 0 and p[1] > 0]
    if not all_points:
        raise ValueError(f"no positive plot points for {path}")
    lx = [math.log10(x) for x, _ in all_points]
    ly = [math.log10(y) for _, y in all_points]
    x0, x1 = min(lx), max(lx)
    y0, y1 = min(ly), max(ly)
    if x0 == x1: x0 -= .5; x1 += .5
    if y0 == y1: y0 -= .5; y1 += .5
    xpad, ypad = max(.04, .03 * (x1-x0)), max(.08, .08 * (y1-y0))
    x0 -= xpad; x1 += xpad; y0 -= ypad; y1 += ypad
    W, H = 980, 640
    left, right, top, bottom = 105, 35, 55, 95
    pw, ph = W-left-right, H-top-bottom
    def xy(x, y):
        return (left + (math.log10(x)-x0)/(x1-x0)*pw,
                top + (y1-math.log10(y))/(y1-y0)*ph)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
           '<rect width="100%" height="100%" fill="white"/>',
           f'<text x="{W/2}" y="28" text-anchor="middle" font-family="sans-serif" font-size="19">{title}</text>']
    for e in range(math.ceil(x0), math.floor(x1)+1):
        v = 10.0**e
        px, _ = xy(v, 10.0**y0)
        out += [f'<line x1="{px:.2f}" y1="{top}" x2="{px:.2f}" y2="{top+ph}" stroke="#e4e4e4"/>',
                f'<text x="{px:.2f}" y="{top+ph+23}" text-anchor="middle" font-family="sans-serif" font-size="12">10^{e}</text>']
    for e in range(math.floor(y0)-1, math.ceil(y1)+1):
        for m in (1,2,5):
            v=m*(10.0**e)
            lv=math.log10(v)
            if not (y0 <= lv <= y1):
                continue
            _, py = xy(10.0**x0, v)
            label=f"10^{e}" if m==1 else f"{m}×10^{e}"
            out += [f'<line x1="{left}" y1="{py:.2f}" x2="{left+pw}" y2="{py:.2f}" stroke="#e4e4e4"/>',
                    f'<text x="{left-10}" y="{py+4:.2f}" text-anchor="end" font-family="sans-serif" font-size="12">{label}</text>']
    for name, pts, color in series:
        valid = [(x,y) for x,y in pts if x>0 and y>0]
        ps = " ".join(f"{xy(x,y)[0]:.2f},{xy(x,y)[1]:.2f}" for x,y in valid)
        out.append(f'<polyline fill="none" stroke="{color}" stroke-width="2" points="{ps}"/>')
        for x,y in valid[::max(1, len(valid)//80)]:
            px,py=xy(x,y); out.append(f'<circle cx="{px:.2f}" cy="{py:.2f}" r="2.2" fill="{color}"/>')
    for x,y in marks:
        if x>0 and y>0:
            px,py=xy(x,y); out.append(f'<circle cx="{px:.2f}" cy="{py:.2f}" r="4.1" fill="#d62728" stroke="white" stroke-width="1"/>')
    out += [f'<line x1="{left}" y1="{top}" x2="{left}" y2="{top+ph}" stroke="#333"/>',
            f'<line x1="{left}" y1="{top+ph}" x2="{left+pw}" y2="{top+ph}" stroke="#333"/>',
            f'<text x="{left+pw/2}" y="{H-23}" text-anchor="middle" font-family="sans-serif" font-size="14">{xlabel} (log scale)</text>',
            f'<text x="23" y="{top+ph/2}" transform="rotate(-90 23 {top+ph/2})" text-anchor="middle" font-family="sans-serif" font-size="14">{ylabel} (log scale)</text>']
    legend_y = top + 18
    for i,(name,_,color) in enumerate(series):
        yy=legend_y+i*20
        out += [f'<line x1="{left+14}" y1="{yy}" x2="{left+42}" y2="{yy}" stroke="{color}" stroke-width="3"/>',
                f'<text x="{left+49}" y="{yy+4}" font-family="sans-serif" font-size="12">{name}</text>']
    if marks:
        yy=legend_y+len(series)*20
        out += [f'<circle cx="{left+28}" cy="{yy}" r="4" fill="#d62728"/>',
                f'<text x="{left+49}" y="{yy+4}" font-family="sans-serif" font-size="12">S crossings ({len(marks)} points)</text>']
    elif note:
        yy=legend_y+len(series)*20
        out += [f'<line x1="{left+24}" y1="{yy-4}" x2="{left+32}" y2="{yy+4}" stroke="#d62728" stroke-width="2"/>',
                f'<line x1="{left+24}" y1="{yy+4}" x2="{left+32}" y2="{yy-4}" stroke="#d62728" stroke-width="2"/>',
                f'<text x="{left+49}" y="{yy+4}" font-family="sans-serif" font-size="12">S: empty in this full-H domain</text>']
    if note:
        out.append(f'<text x="{left+pw-5}" y="{top+18}" text-anchor="end" font-family="sans-serif" font-size="12" fill="#555">{note}</text>')
    out.append('</svg>')
    path.write_text("\n".join(out)+"\n", encoding="utf-8")


def main():
    out = HERE
    crossings = [int(r["N"]) for r in rows_csv(out / "core_crossings.csv")]
    cross_rows = list(rows_csv(out / "core_crossings.csv"))
    crossing_set = set(crossings)
    scan_runner=json.loads((out/"core_runner_metadata_scan.json").read_text())
    full_runner=json.loads((out/"core_runner_metadata_full.json").read_text())
    source_hash_match=(scan_runner["native_source_sha256"]==full_runner["native_source_sha256"])
    if not source_hash_match:
        raise RuntimeError("scan and full-core outputs do not share the same native source hash")
    compiler=scan_runner["build_command"][0]
    probe=subprocess.run([compiler,"-dM","-E","-x","c++","-include","cfloat","/dev/null"],
                         check=True,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT).stdout
    m=re.search(r"#define __LDBL_MANT_DIG__ (\d+)",probe)
    if not m:
        raise RuntimeError("could not verify native long-double mantissa from compiler macros")
    ld_bits=int(m.group(1))
    scan_meta=json.loads((out/"core_scan_metadata.json").read_text())
    scan_meta["native_long_double_mantissa_bits"]=ld_bits
    scan_meta["head_and_plant_arithmetic"]=(f"platform C++ long double ({ld_bits}-bit mantissa) with Kahan prefix sums; diagnostic, not certified")
    endpoint_n=scan_meta["endpoint_b_computed"]
    signs_file=next(out.glob("core_signs_*.csv.gz"))
    signs_bytes=signs_file.stat().st_size
    if signs_bytes>40*1024*1024:
        raise RuntimeError(f"compressed sign chunk exceeds 40 MiB: {signs_bytes}")
    endpoint_sign=None; sign_rows=0; unresolved_signs=0; next_sign_n=3
    with gzip.open(signs_file,"rt",newline="",encoding="ascii") as f:
        for r in csv.DictReader(f):
            n=int(r["N"])
            if n!=next_sign_n:
                raise RuntimeError(f"sign coverage gap/duplicate at N={n}, expected {next_sign_n}")
            sign_rows+=1; next_sign_n+=1
            if r["b_sign_certified"]=="UNRESOLVED": unresolved_signs+=1
            if n==endpoint_n:
                endpoint_sign=r["b_sign_certified"]
    if endpoint_sign not in ("+1","-1") or unresolved_signs:
        raise RuntimeError("endpoint sign is absent or uncertified")
    scan_meta["endpoint_b_sign_certified"]=endpoint_sign
    scan_meta["endpoint_membership_use"]=f"b_{endpoint_n} sign used to classify S at N={endpoint_n-1}"
    (out/"core_scan_metadata.json").write_text(json.dumps(scan_meta,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    (out/"core_endpoint.csv").write_text(
        "N,b_sign_certified,MPFR_precision_bits,role\n"
        f"{endpoint_n},{endpoint_sign},{scan_meta['mpfr_last_precision_bits']},endpoint_membership\n",
        encoding="ascii")
    full_rows = list(rows_csv(out / "core_full_H.csv"))
    full_by_n = {int(r["N"]): r for r in full_rows}
    if len(full_by_n)!=len(full_rows) or len(full_rows)!=92:
        raise RuntimeError("full-H grid output is not 92 unique rows")

    # Sparse log sampling for plotting; all scan values remain in the gzip CSVs.
    targets = {round(math.exp(math.log(3) + (math.log(10_000_000)-math.log(3))*i/1499))
               for i in range(1500)}
    want = targets | crossing_set | {n+1 for n in crossing_set}
    scan_points: dict[int, dict] = {}
    scan_files=sorted(out.glob("core_scan_[0-9]*.csv.gz"))
    scan_rows=0; next_scan_n=3
    max_chunk_bytes=max((p.stat().st_size for p in scan_files),default=0)
    for file in scan_files:
        with gzip.open(file, "rt", newline="", encoding="ascii") as f:
            for r in csv.DictReader(f):
                n=int(r["N"])
                if n!=next_scan_n:
                    raise RuntimeError(f"scan coverage gap/duplicate at N={n}, expected {next_scan_n}")
                scan_rows+=1; next_scan_n+=1
                if n in want:
                    scan_points[n] = {k: float(v) if k!="N" else n for k,v in r.items()}
    if scan_rows!=9_999_998 or next_scan_n!=10_000_001:
        raise RuntimeError(f"scan row coverage mismatch: {scan_rows}, next={next_scan_n}")
    if max_chunk_bytes>40*1024*1024:
        raise RuntimeError(f"compressed scan chunk exceeds 40 MiB: {max_chunk_bytes}")
    if sign_rows!=9_999_999:
        raise RuntimeError(f"sign coverage mismatch: {sign_rows}")

    crossing_values=[]
    for r in cross_rows:
        n=int(r["N"]); cur=scan_points[n]; nxt=scan_points[n+1]
        crossing_values.append({
            "N":n,"bN":cur["b_approx_long_double"],"bN1":nxt["b_approx_long_double"],
            "bN_sign":r["bN_sign"],"bN1_sign":r["bN1_sign"],
            "head":cur["head_approx_long_double"],"head_logN":cur["head_times_logN"],
            "full_H":"UNAVAILABLE" if n not in full_by_n else full_by_n[n]["full_H"],
            "shoulder":"UNAVAILABLE" if n not in full_by_n else full_by_n[n]["shoulder"],
        })
    with (out/"core_crossing_values.csv").open("w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=list(crossing_values[0].keys()))
        w.writeheader(); w.writerows(crossing_values)

    decade_starts=[3,10,100,1000,10000,100000,1000000]
    decade_ends=[9,99,999,9999,99999,999999,10000000]
    decade_rows=[]
    for lo,hi in zip(decade_starts,decade_ends):
        vals=[r for r in crossing_values if lo<=r["N"]<=hi]
        hmin,hmax=safe_range(r["head"] for r in vals)
        hlmin,hlmax=safe_range(r["head_logN"] for r in vals)
        fullvals=[r for r in vals if r["full_H"]!="UNAVAILABLE"]
        shmin,shmax=safe_range(float(r["shoulder"]) for r in fullvals)
        fmin,fmax=safe_range(float(r["full_H"]) for r in fullvals)
        if not vals:
            full_status="NO_S_IN_DECADE"
        elif hi<=10000 and not fullvals:
            full_status="NO_S_IN_DECADE"
        else:
            full_status="UNAVAILABLE_FULL_SHOULDER_NOT_COMPUTED"
        decade_rows.append({
            "decade_start":lo,"decade_end":hi,"S_count":len(vals),
            "min_head_on_S":hmin,"max_head_on_S":hmax,
            "min_head_logN_on_S":hlmin,"max_head_logN_on_S":hlmax,
            "full_H_status_on_S":full_status,"min_full_H_on_S":fmin,"max_full_H_on_S":fmax,
            "shoulder_status_on_S":full_status,"min_shoulder_on_S":shmin,"max_shoulder_on_S":shmax,
        })
    with (out/"core_decade_summary.csv").open("w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=list(decade_rows[0].keys())); w.writeheader();w.writerows(decade_rows)

    grid_rows=[r for r in full_rows if r["log_grid"]=="true"]
    grid_by_decade=[]
    for lo,hi in zip(decade_starts,decade_ends):
        vals=[r for r in grid_rows if lo<=int(r["N"])<=hi]
        if not vals: continue
        for key in ("head","shoulder","full_H"):
            mn,mx=safe_range(r[key] for r in vals)
            if key=="head": hmin,hmax=mn,mx
            elif key=="shoulder": smin,smax=mn,mx
            else: fmin,fmax=mn,mx
        grid_by_decade.append({"decade_start":lo,"decade_end":hi,"grid_points":len(vals),
                               "min_head":hmin,"max_head":hmax,"min_shoulder":smin,"max_shoulder":smax,
                               "min_full_H":fmin,"max_full_H":fmax})
    with (out/"core_grid_summary.csv").open("w",newline="",encoding="utf-8") as f:
        w=csv.DictWriter(f,fieldnames=list(grid_by_decade[0].keys()));w.writeheader();w.writerows(grid_by_decade)

    # J4 analytic plant and the exact discrete prefix values produced by C++.
    j4=list(rows_csv(out/"core_j4.csv"))
    for r in j4:
        for key in r:
            if key!="N": r[key]=float(r[key])
        r["N"]=int(r["N"])
    full_slope=log_slope(j4,"planted_head")
    self_slope=log_slope(j4,"plant_self")
    corr_full_slope=log_slope([{**r,"corrected":r["planted_head"]*r["logN"]**2} for r in j4],"corrected")
    corr_self_slope=log_slope([{**r,"corrected":r["plant_self"]*r["logN"]**2} for r in j4],"corrected")
    f1=60.0/1789.0
    rho_a=5.0/6.0; denom=rho_a*rho_a+49
    f1_formula=2*rho_a/denom
    slope_diff=abs(full_slope-self_slope)
    j4_status="HIT" if slope_diff<=0.05 and abs(f1-f1_formula)<1e-15 else "MISS"
    j4_obj={
        "status":j4_status,
        "N_window":[100000,10000000],"grid_points":len(j4),
        "rho":"5/6+7i","plant":"f(k)=2 Re(k^rho/rho), inserted literally with unchanged s_N",
        "f1_exact":"60/1789","f1_formula_float":f1_formula,"no_offset_check_abs_diff":abs(f1-f1_formula),
        "raw_planted_head_log_slope":full_slope,"raw_discrete_self_term_log_slope":self_slope,
        "abs_slope_difference":slope_diff,"preregistered_gate":0.05,
        "raw_gate":"PASS" if slope_diff<=0.05 else "FAIL",
        "log_squared_corrected_planted_head_slope":corr_full_slope,
        "log_squared_corrected_discrete_self_slope":corr_self_slope,
        "analytic_power_exponent":"2/3",
        "nonoscillatory_local_log_slope":"2/3-2/log(N)",
        "self_energy_leading_formula":"(108/1789) N^(2/3)/log(N)^2 * [1+cos(14 log N-2 atan(42/5)-atan(21))/sqrt(442)] + O(log(N)^-2)",
        "planted_prefix":"exact discrete prefix sum over every k from 1 through N; includes f(1), no centering/subtraction",
        "scope":"finite planted-control diagnostic; no asymptotic conclusion about original H_N",
    }
    (out/"core_j4_analysis.json").write_text(json.dumps(j4_obj,indent=2,sort_keys=True)+"\n",encoding="utf-8")

    # Score the source-frozen P3-P6 rules from this Part 2 scan.
    s_under_1e4=sum(3<=n<=10000 for n in crossings)
    early_decades=[(3,9),(10,99),(100,999),(1000,9999)]
    nonempty_early=all(any(lo<=n<=hi for n in crossings) for lo,hi in early_decades)
    p3="HIT" if s_under_1e4>=10 and nonempty_early and all(any(lo<=n<=hi for n in crossings) for lo,hi in [(10000,99999),(100000,999999),(1000000,10000000)]) else "MISS"
    p4_values=[r for r in crossing_values if 1000<=r["N"]<=10000]
    p4="HIT" if p4_values and max(float(r["full_H"]) for r in p4_values if r["full_H"]!="UNAVAILABLE")<=1 else "MISS"
    p5_values=[r["head_logN"] for r in crossing_values if r["N"]>=10000]
    p5="HIT" if p5_values and all(0.02<=v<=0.3 for v in p5_values) else "MISS"
    j3=json.loads((out/"core_j3_judge.json").read_text())
    judges={
        "P3":{"score":p3,"p":0.7,"observed_S_3_to_10000":s_under_1e4,"required_minimum":10,
              "every_decade_3_to_1e7_nonempty":nonempty_early and all(any(lo<=n<=hi for n in crossings) for lo,hi in [(10000,99999),(100000,999999),(1000000,10000000)]),
              "decade_counts":[{"start":lo,"end":hi,"count":sum(lo<=n<=hi for n in crossings)} for lo,hi in zip(decade_starts,decade_ends)]},
        "P4":{"score":p4,"p":0.75,"S_intersection_1000_to_10000":len(p4_values),
              "status":"NOT_TESTABLE_EMPTY_SET" if not p4_values else "TESTED",
              "max_full_H":None if not p4_values else max(float(r["full_H"]) for r in p4_values if r["full_H"]!="UNAVAILABLE")},
        "P5":{"score":p5,"p":0.45,"number_of_S_values_N_ge_10000":len(p5_values),
              "min_head_logN":min(p5_values) if p5_values else None,"max_head_logN":max(p5_values) if p5_values else None,
              "required_interval":[0.02,0.3],"interpretation":"finite scan range only; no asymptotic equivalence inferred"},
        "P6":{"score":j4_status,"p":0.9,"judge":"J4","abs_raw_slope_difference":slope_diff,
              "gate":0.05,"discrete_self_term_is_reference":True},
        "J3_finite_identity":{"status":j3["finite_identity_status"],"max_abs_difference":j3["max_abs_difference"],
                              "scope":"clarified finite subjudge only; infinite tail not independently summed"},
        "honesty":{"RH_PROVED":False,"PX_RH_CLAIM":"NOT_MADE","route":"CHALLENGER_NOT_RH"},
    }
    (out/"core_judges.json").write_text(json.dumps(judges,indent=2,sort_keys=True)+"\n",encoding="utf-8")

    # Log-grid data and S-marked plots. Full H has no S marker because the
    # certified scan found no S point in the only full-H interval [3,10000].
    with (out/"core_full_grid_points.csv").open("w",newline="",encoding="utf-8") as f:
        fields=["N","in_S","K","head","shoulder","full_H","head_times_logN","shoulder_times_logN","full_H_times_logN"]
        w=csv.DictWriter(f,fieldnames=fields);w.writeheader()
        for r in grid_rows:
            n=int(r["N"]); l=math.log(n)
            w.writerow({"N":n,"in_S":r["in_S"],"K":r["K"],"head":r["head"],"shoulder":r["shoulder"],
                        "full_H":r["full_H"],"head_times_logN":float(r["head"])*l,
                        "shoulder_times_logN":float(r["shoulder"])*l,"full_H_times_logN":float(r["full_H"])*l})
    full_pts=[(int(r["N"]),float(r["full_H"])) for r in grid_rows]
    full_marks=[(int(r["N"]),float(r["full_H"])) for r in grid_rows if r["in_S"]=="true"]
    grid_note="S empty in full-H domain" if not full_marks else None
    svg_plot(out/"core_full_H_vs_N.svg","Full H_N vs N (92-point grid)","N","H_N",
             [("Full H_N (head + full shoulder)",full_pts,"#2563a6")],full_marks,grid_note)
    svg_plot(out/"core_full_Hlog_vs_N.svg","Full H_N log(N) vs N (92-point grid)","N","H_N log(N)",
             [("Full H_N log(N)",[(x,y*math.log(x)) for x,y in full_pts],"#2563a6")],
             [(x,y*math.log(x)) for x,y in full_marks],grid_note)
    head_plot=sorted((n,r["head_approx_long_double"]) for n,r in scan_points.items() if n in targets)
    head_marks=[(r["N"],r["head"]) for r in crossing_values]
    svg_plot(out/"core_head_H_vs_N.svg","Head H_N vs N (log display grid)","N","Head part",
             [("head H_N",head_plot,"#246b8e")],head_marks,"1500 rounded display targets + every S point")
    svg_plot(out/"core_head_Hlog_vs_N.svg","Head H_N log(N) vs N (log display grid)","N","Head part log(N)",
             [("head H_N log(N)",[(x,y*math.log(x)) for x,y in head_plot],"#246b8e")],
             [(x,y*math.log(x)) for x,y in head_marks],"1500 rounded display targets + every S point")

    # Minimal run metadata for this analysis step.
    analysis_meta={
        "python":sys.version,"platform":platform.platform(),"compressed_scan_chunks":len(list(out.glob("core_scan_[0-9]*.csv.gz"))),
        "native_long_double_mantissa_bits":ld_bits,
        "scan_rows_expected":9_999_998,"scan_points_read_for_plot":len(scan_points),"S_count":len(crossings),
        "scan_rows_verified_contiguous":scan_rows,"sign_rows_verified_contiguous":sign_rows,
        "max_scan_chunk_bytes":max_chunk_bytes,"sign_file_bytes":signs_bytes,
        "source_hash_match_scan_full":source_hash_match,
        "full_H_grid_rows":len(full_rows),"unresolved_b_signs":unresolved_signs,
        "full_grid_points_in_summary":len(grid_rows),"full_H_S_rows":len(full_marks),
        "rounding":"100 source log-grid points rounded to integers then deduplicated to 92 unique N values",
        "display_decimation":"1500 rounded logarithmic head plot targets; source CSV remains un-decimated",
    }
    (out/"core_analysis_metadata.json").write_text(json.dumps(analysis_meta,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    (out/"core_artifact_check.json").write_text(json.dumps({
        "scan_rows_3_to_10000000":scan_rows,
        "sign_rows_3_to_10000001":sign_rows,
        "scan_contiguous":True,"signs_contiguous":True,
        "endpoint_sign_certified":endpoint_sign,
        "unresolved_signs":unresolved_signs,
        "max_compressed_scan_chunk_bytes":max_chunk_bytes,"chunk_limit_bytes":40*1024*1024,
        "sign_file_bytes":signs_bytes,
        "full_H_grid_rows":len(full_rows),"full_H_unique_N":len(full_by_n),
        "scan_full_source_hash_match":source_hash_match,
        "J3_finite_identity_rows":198,
        "J3_finite_identity_status":json.loads((out/"core_j3_judge.json").read_text())["finite_identity_status"],
    },indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"S_count":len(crossings),"full_grid_rows":len(grid_rows),"J3":j3["finite_identity_status"],
                      "J4":j4_status,"P3":p3,"P4":p4,"P5":p5,"P6":j4_status,
                      "P5_min_max":safe_range(p5_values),"J4_abs_slope_diff":slope_diff},indent=2))


if __name__ == "__main__":
    main()
