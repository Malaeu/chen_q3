#!/usr/bin/env python3
"""Exhaustive B+ scalar corner diagnostics, 296-bit MPFR, no K scoring."""
import csv
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

sys.path.insert(0,"/workspace/conditioning_deps")
import gmpy2 as g
from flint import arb,acb,ctx

HERE=Path(__file__).resolve().parent
PACKET=HERE.parent
SOURCE=PACKET/"inputs/analytic_source.py"
EXPECTED_SOURCE_SHA="4e26ed90c8ef7305699802c02490bb0cea0da26be49891c98d387b5210eb8f63"
BITS=256
WORK=296
MAXM=3000
F=g.mpfr


def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def context():
    g.get_context().precision=WORK
    ctx.prec=BITS+72


def setup(source):
    context()
    # These are the pinned source's OWN coefficients, including signed DH
    # composite atoms. No replacement recurrence or prime-only DH is used.
    zeta,dh=source.coefficients(MAXM,BITS)
    out={"pi":g.const_pi(),"cut":g.exp2(-304),"worlds":{}}
    for world,b,alpha in (("zeta",zeta,F(".5")),("dh",dh,F("1.5"))):
        s0=[F(0)]*(MAXM+1);s1=[F(0)]*(MAXM+1)
        for n in range(2,MAXM+1):
            v=b[n]/g.sqrt(n)
            s0[n]=s0[n-1]+v
            s1[n]=s1[n-1]+v*g.log(n)
        digits=int((BITS+48)*.30103)+12
        tri=F(acb(arb(str(alpha/2))).polygamma(1).real.mid().str(digits,radius=False))
        out["worlds"][world]={"S0":s0,"S1":s1,"alpha":alpha,"trigamma":tri,
                              "coefficient_b6":str(b[6])}
    return out


def components00(m,world,state):
    context()
    ll=g.log(m);s=state["worlds"][world]
    aa=s["alpha"];ee=g.exp(-aa*ll);step=g.exp(-2*ll)
    t1=F(0);t2=F(0);terms=0
    while ee>state["cut"]:
        t1+=ee/(aa*aa);t2+=ee/aa
        aa+=2;ee*=step;terms+=1
    pi=state["pi"]
    c=-g.const_euler()-g.log(8*pi/(5 if world=="dh" else 1))
    c+=pi/2 if world=="dh" else -pi/2
    endpoint=g.exp(-ll/2)
    tail=g.atanh(endpoint)+(-g.atan(endpoint) if world=="dh" else g.atan(endpoint))
    hh=c+s["trigamma"]/(2*ll)-2*t1/ll-2*t2+2*tail
    bb=2*(s["S0"][m-1]-s["S1"][m-1]/ll)
    pole=F(0) if world=="dh" else 32*g.sinh(ll/4)**2/ll
    native=hh+pole-bb
    tm=(1+(1+g.log(ll))/(4*ll))*2*pi*m/ll
    return dict(L=ll,T=tm,H00=hh,B00=bb,pole00=pole,native=native,tail_terms=terms)


def q00(a,gamma,ll):
    # Exact rational 1/3 and 9/10 are constructed by division in MPFR.
    alpha=F(1)/3 if a=="1/3" else F(a)
    z=g.mpc(gamma,alpha)
    coefficient=2*g.sin(z*ll/2)/(g.sqrt(ll)*z)
    return 4*(coefficient*coefficient).real


def main():
    cpu=time.process_time();wall=time.perf_counter()
    assert sha(SOURCE)==EXPECTED_SOURCE_SHA,"PINNED_SOURCE_HASH_MISMATCH"
    receipt=json.loads((PACKET/"ADDENDUM_PRE_RUN_RECEIPT.json").read_text())
    assert receipt["confirmed_remote"]
    assert sha(PACKET/"PREDICTIONS.md")==receipt["prediction_sha256"]
    gate=json.loads((PACKET/"gate/gate.json").read_text())
    assert gate["pass"] and gate["positive_a_cells_passed"]==12
    spec=importlib.util.spec_from_file_location("_Bplus_scalar_pinned_source",SOURCE)
    source=importlib.util.module_from_spec(spec);spec.loader.exec_module(source)
    state=setup(source)
    # Fresh complete pinned source, both worlds. Compare u=1, Q=0 directly.
    original,meta=source.build(80,BITS)
    comparisons=[]
    for world in ("zeta","dh"):
        fresh=components00(80,world,state)
        expected=original[world][0][0,0]
        error=abs(fresh["native"]-expected)
        assert error<F("1e-60"),(world,str(error))
        comparisons.append({"world":world,"m":80,"scalar":str(fresh["native"]),
                            "fresh_pinned_build_00":str(expected),"absolute_difference":str(error),
                            "pass":True})
    del original
    validation={"status":"PASS_FRESH_PINNED_SOURCE80_BOTH_WORLDS", "bits":BITS,"working_bits":WORK,
                "source_meta":meta,"comparisons":comparisons,"source_sha256":sha(SOURCE),
                "source_git_blob":"27bbaabbc5938b3157b5bc20f5e6db2f882122c0"}
    (HERE/"scalar_validation.json").write_text(json.dumps(validation,indent=2)+"\n")

    cases=[("zeta","0",0)]+[("zeta",a,height) for a in ("0.05","0.1","1/3") for height in (14,50)]+[("dh","0",0)]
    summaries={}
    for world,a,height in cases:
        key=f"{world}_a{a}_gamma{height}"
        summaries[key]={"world":world,"u":"9/10" if world=="zeta" else "1",
                        "a":a,"gamma":height,"m_admit":None,"first_negative_m":None,
                        "tested_count":0,"negative_count":0,"zero_count":0,"minimum":None,"minimum_m":None}
    fields=["m","world","u","a","gamma","L","T","H00","pole00","B00","Q00","corner","negative","native_u1_corner","tail_terms"]
    zeta_control_min=None;zeta_control_min_m=None;rows=0
    with (HERE/"scalar_corners.csv").open("w",newline="") as f:
        writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
        for m in range(16,MAXM+1):
            # Fixed MPFR context is restored even after full source validation.
            vals={world:components00(m,world,state) for world in ("zeta","dh")}
            assert vals["zeta"]["native"]>0,("ORIGINAL_ZETA_NATIVE_CORNER_CONTROL_FAILED",m,str(vals["zeta"]["native"]))
            if zeta_control_min is None or vals["zeta"]["native"]<zeta_control_min:
                zeta_control_min=vals["zeta"]["native"];zeta_control_min_m=m
            for world,a,height in cases:
                vv=vals[world]
                if height and vv["T"]<=height:continue
                uu=F(9)/10 if world=="zeta" else F(1)
                qq=F(0) if not height else q00(a,height,vv["L"])
                total=vv["H00"]+vv["pole00"]-uu*vv["B00"]+qq
                negative=bool(total<0)
                q=summaries[f"{world}_a{a}_gamma{height}"]
                if q["m_admit"] is None:q["m_admit"]=m
                if negative and q["first_negative_m"] is None:q["first_negative_m"]=m
                if q["minimum"] is None or total<F(q["minimum"]):q["minimum"]=str(total);q["minimum_m"]=m
                q["tested_count"]+=1;q["negative_count"]+=int(negative);q["zero_count"]+=int(total==0)
                writer.writerow({"m":m,"world":world,"u":q["u"],"a":a,"gamma":height,
                                 "L":str(vv["L"]),"T":str(vv["T"]),"H00":str(vv["H00"]),"pole00":str(vv["pole00"]),
                                 "B00":str(vv["B00"]),"Q00":str(qq),"corner":str(total),"negative":negative,
                                 "native_u1_corner":str(vv["native"]),"tail_terms":vv["tail_terms"]})
                rows+=1
            if m%500==0:print(json.dumps({"scalar_through_m":m,"cpu_seconds":time.process_time()-cpu}),flush=True)
    for q in summaries.values():
        q["threshold_report"]=q["first_negative_m"] if q["first_negative_m"] is not None else ">3000"
        q["censored"]=q["first_negative_m"] is None
    summary={"schema":"corner_Bplus_exhaustive_scalar.v1","status":"COMPLETE_EXHAUSTIVE_INTEGER_SCAN",
             "honesty":"DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER_NOT_RH; PX_RH_CLAIM_NOT_MADE",
             "m_min":16,"m_max":MAXM,"source_bits":BITS,"actual_working_bits":WORK,
             "decimal_working_precision":WORK*.3010299956639812,"special_function_bits":BITS+72,
             "tail_cut":"2^-304","strict_negative_threshold":"0, using MPFR comparison; no float conversion",
             "cases":list(summaries.values()),"rows":rows,"expected_rows":sum(q["tested_count"] for q in summaries.values()),
             "controls":{"fresh_pinned_source80_both_worlds_pass":True,"original_zeta_u1_native_corner_positive_all_m":True,
                         "original_zeta_minimum":str(zeta_control_min),"original_zeta_minimum_m":zeta_control_min_m,
                         "DH_pole00_exactly_zero":True,"changed_zeta_u0.9_not_required_positive":True},
             "budget":{"remaining_CPU_seconds":240,"actual_process_CPU_seconds":time.process_time()-cpu,"actual_wall_seconds":time.perf_counter()-wall},
             "provenance":{"prediction_commit":receipt["prediction_commit"],"prediction_sha256":receipt["prediction_sha256"],
                           "source_relative_path":"inputs/analytic_source.py","source_sha256":sha(SOURCE),
                           "source_git_blob":"27bbaabbc5938b3157b5bc20f5e6db2f882122c0",
                           "coefficient_producer":"unchanged analytic_source.coefficients(3000,256)",
                           "driver_sha256":sha(__file__),"physical_kernel_gate_pass":True},
             "limits":["Finite exhaustive scalar diagnostics, not a cofinal proof or certified enclosure.",
                       "No K scoring is performed.","Gamma50 cases begin at first strict T_m>50, m21."]}
    assert rows==sum(q["tested_count"] for q in summaries.values())
    (HERE/"scalar_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(json.dumps({"status":summary["status"],"rows":rows,"budget":summary["budget"],"cases":[{k:q[k] for k in ("world","a","gamma","threshold_report")} for q in summaries.values()]}),flush=True)


if __name__=="__main__":main()
