#!/usr/bin/env python3
"""B+ finite core diagnostics. No prediction scoring or cofinal conclusion."""
import argparse
import csv
import hashlib
import importlib
import json
import os
from pathlib import Path
import sys
import time

import numpy as np
from scipy.linalg import eigh, null_space
from scipy.sparse.linalg import LinearOperator, eigsh

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent
sys.path.insert(0, str(PACKET / "builder"))
GRID = sorted({16,32,50,51,54,64,80,128,208,256,512,750,1000,1500,2000,3000,
               23,29,31,157,162,857,861,862})
PLANTS = [(a,g) for a in ("0.05","0.1","1/3") for g in (14,50)]
THRESHOLD = -1e-6


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def save_json(p, obj):
    def scalar(x):
        if isinstance(x,np.generic):return x.item()
        raise TypeError(type(x).__name__)
    p.write_text(json.dumps(obj, indent=2, allow_nan=False,default=scalar)+"\n")


class Restriction:
    """R=I-2vv^T maps the normalized constraint to the first coordinate."""
    def __init__(self, q):
        self.n = len(q)
        self.q = np.asarray(q)
        norm = np.linalg.norm(q)
        self.full = norm == 0
        self.dim = self.n if self.full else self.n-1
        self.v = None
        if not self.full:
            u = q/norm
            v = u.copy()
            v[0] += 1 if u[0] >= 0 else -1
            self.v = v/np.linalg.norm(v)

    def reflect(self, y):
        return y if self.full else y-2*self.v*np.dot(self.v,y)

    def embed(self, x):
        return x if self.full else self.reflect(np.r_[0.,x])

    def reduce(self, y):
        return y if self.full else self.reflect(y)[1:]

    def matrix(self):
        if self.full:
            return np.eye(self.n)
        return (np.eye(self.n)-2*np.outer(self.v,self.v))[:,1:]


def coefficient(m, a, gamma):
    """Stable source coefficient using non-normalized complex sinc."""
    ld = np.longdouble
    ll = np.log(ld(m))
    pi = np.arccos(ld(-1))
    j = np.arange(m+1)
    w = 2*pi*j/ll
    alpha = ld(1)/3 if a == "1/3" else ld(a)
    zz = np.clongdouble(complex(gamma,0))+np.clongdouble(1j)*alpha
    def sinc(t):
        out = np.ones_like(t)
        mask = t != 0
        out[mask] = np.sin(t[mask])/t[mask]
        return out
    d = np.where(j==0, ld(1), np.sqrt(ld(2)))
    return np.asarray(d*((-1)**j)*np.sqrt(ll)/2 *
                      (sinc((zz-w)*ll/2)+sinc((zz+w)*ll/2)), dtype=complex)


def extremum(matrix, restriction, *, which, updates=()):
    """Extreme Ritz pair of the exact supplied finite matrix restriction."""
    def full_mv(y):
        out = matrix@y
        for scale, v in updates:
            out += scale*v*np.dot(v,y)
        return out
    def mv(x):
        return restriction.reduce(full_mv(restriction.embed(x)))
    dim = restriction.dim
    op = LinearOperator((dim,dim), matvec=mv, dtype=float)
    if dim <= 128:
        basis = restriction.matrix()
        dense = basis.T@matrix@basis
        for scale,v in updates:
            rv = basis.T@v
            dense += scale*np.outer(rv,rv)
        idx = [0,0] if which == "SA" else [dim-1,dim-1]
        value, vec = eigh(dense, subset_by_index=idx, driver="evr")
        value, vec = float(value[0]), vec[:,0]
        solver = "scipy.linalg.eigh subset evr"
    else:
        v0 = np.random.default_rng(20261104).normal(size=dim)
        value, vec = eigsh(op, k=1, which=which, tol=1e-11,
                           maxiter=1000, ncv=min(40,dim), v0=v0)
        value, vec = float(value[0]), vec[:,0]
        solver = "scipy.sparse.linalg.eigsh full-matrix operator"
    residual = float(np.linalg.norm(mv(vec)-value*vec))
    if residual > 5e-9:
        raise RuntimeError(f"EIGENPAIR_RESIDUAL_TOO_LARGE {residual}")
    y = restriction.embed(vec)
    qnorm = np.linalg.norm(restriction.q)
    cres = 0. if qnorm == 0 else abs(float(np.dot(restriction.q,y)))/qnorm
    return {"value": value,"solver":solver,"eigenpair_residual":residual,
            "normalized_constraint_residual":cres}, y


def small_gate(builder):
    """Independent physical null-space generalized-eigh check at m=16."""
    records=[]
    for world in ("zeta","dh"):
        part, meta = builder.build(16,world=world)
        s = 1/np.sqrt(part["W"])
        p = part["p"]
        q = s*p
        rr = Restriction(q)
        physical_basis = np.eye(17) if np.linalg.norm(p)==0 else null_space(p[None,:])
        wb = physical_basis.T@(part["W"][:,None]*physical_basis)
        source_p = np.sqrt(2/np.log(16))*np.where(np.arange(17)==0,1.,np.sqrt(2.))*np.sinh(np.log(16)/4)/(part["omega"]**2+.25)
        if world=="dh": source_p[:]=0
        for kind in ("Bmax","weakmin"):
            mm = part["B"] if kind=="Bmax" else part["H"]+np.outer(p,p)-.9*part["B"]
            sm = s[:,None]*mm*s[None,:]
            got,y = extremum(sm,rr,which="LA" if kind=="Bmax" else "SA")
            gb = physical_basis.T@mm@physical_basis
            vals = eigh(gb,wb,eigvals_only=True)
            expected = float(vals[-1] if kind=="Bmax" else vals[0])
            err=abs(got["value"]-expected)
            z=s*y
            literal=Restriction(p)
            literal_value,literal_y=extremum(sm,literal,which="LA" if kind=="Bmax" else "SA")
            rec={"world":world,"kind":kind,"householder_value":got["value"],
                 "physical_null_generalized_eigh_value":expected,"absolute_error":err,
                 "p_dot_physical_z":float(p@z),"W_norm_squared":float(np.dot(z*part["W"],z)),
                 "literal_p_perp_value":literal_value["value"],
                 "literal_p_perp_physical_p_dot_z":float(p@(s*literal_y)),
                 "fresh_p_formula_max_abs_error":float(np.max(np.abs(source_p-p))),
                 "decomposition_max_abs_error":float(np.max(np.abs(part["A"]-(part["H"]+np.outer(p,p)-part["B"])))),
                 "source_meta":meta,"pass":err<=1e-11 and np.max(np.abs(source_p-p))<=1e-12}
            if not rec["pass"]:raise RuntimeError(f"SMALL_GATE_FAILED {rec}")
            records.append(rec)
    # A generic small matrix catches an accidental projection of p in y-space.
    rng=np.random.default_rng(81)
    n=7; p=rng.normal(size=n); w=1+np.arange(n)**2
    mm=rng.normal(size=(n,n));mm=(mm+mm.T)/2;s=1/np.sqrt(w)
    r=Restriction(s*p);b=null_space(p[None,:]);gb=b.T@mm@b;wb=b.T@(w[:,None]*b)
    got,_=extremum(s[:,None]*mm*s[None,:],r,which="LA")
    expected=float(eigh(gb,wb,eigvals_only=True)[-1])
    error=abs(got["value"]-expected)
    assert error<1e-12
    out={"pass":True,"m":16,"source_checks":records,"synthetic_generalized_error":error,
         "scope":"Finite normalization/constraint implementation gate, not arithmetic proof"}
    save_json(HERE/"normalization_gate.json",out)
    return out


def admitted(m,gamma):
    ll=np.log(m)
    return (1+(1+np.log(ll))/(4*ll))*2*np.pi*m/ll > gamma


def run(args):
    builder=importlib.import_module("core_components")
    receipt=json.loads((PACKET/"ADDENDUM_PRE_RUN_RECEIPT.json").read_text())
    if sha(PACKET/"PREDICTIONS.md")!=receipt["prediction_sha256"]:
        raise RuntimeError("ADDENDUM_PREDICTION_HASH_MISMATCH")
    start=time.perf_counter();cpu=time.process_time()
    small_gate(builder)
    rows=[];history=[];firsts={};failures=[];processed=[]
    vectordir=HERE/"weak_vectors";vectordir.mkdir(exist_ok=True)
    requested=sorted(set(args.grid if args.grid else GRID)|{16,21})

    def checkpoint():
        fields=sorted(set().union(*(r.keys() for r in rows))) if rows else []
        if fields:
            with (HERE/"core_cells.csv").open("w",newline="") as f:
                writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader();writer.writerows(rows)
        save_json(HERE/"core_results.json",{
            "schema":"corner_Bplus_core_diagnostic.v1","honesty":"DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER_NOT_RH; PX_RH_CLAIM_NOT_MADE",
            "prediction_commit":receipt["prediction_commit"],"prediction_sha256":receipt["prediction_sha256"],
            "source_pins":{"two_cores_sha256":sha(PACKET/"inputs/PROSHKA_VERDICT_TWO_CORES_2026-11-04.md"),
                           "core_components_sha256":sha(PACKET/"builder/core_components.py"),
                           "driver_sha256":sha(__file__)},
            "requested_core_grid":GRID,"requested_run_grid":requested,"processed_m":processed,
            "rows":rows,"first_weak_detections":firsts,"failures":failures,
            "source_assembly_history":history,
            "budget":{"initial_process_CPU_seconds":args.budget,"actual_process_CPU_seconds":time.process_time()-cpu,
                      "actual_wall_seconds":time.perf_counter()-start},
            "limits":["Finite numeric extreme eigenpairs with residuals, not cofinal proofs.",
                      "No K prediction is scored by this worker.",
                      "B original and B_eff=B-Q are separate rows.",
                      "Literal normalized p-perp is not physical pole-null."]})

    for m in requested:
        if time.process_time()-cpu>=args.budget:
            failures.append({"m":m,"status":"CPU_BUDGET_EXHAUSTED_BEFORE_CELL"});break
        try:
            for world in ("zeta","dh"):
                part,meta=builder.build(m,world=world)
                history.append({"m":m,"world":world,"meta":meta})
                s=1/np.sqrt(part["W"]);p=part["p"]
                primary=Restriction(s*p);literal=Restriction(p)
                base=s[:,None]*part["B"]*s[None,:]
                orig,y=extremum(base,primary,which="LA")
                rows.append(dict(m=m,world=world,kind="Cstar_original_B",a="0",gamma="",convention="physical_pole_null" if world=="zeta" else "DH_full_carrier",**orig))
                if world=="dh":continue
                # Weak matrix retains physical pole before either restriction.
                weak=s[:,None]*part["H"]*s[None,:]+np.outer(s*p,s*p)-.9*base
                for a,gamma in [("0",0)]+PLANTS:
                    if gamma and not admitted(m,gamma):continue
                    if gamma:
                        c=coefficient(m,a,gamma);r=s*c.real;t=s*c.imag
                        eff,y=extremum(base,primary,which="LA",updates=((-4,r),(4,t)))
                        rows.append(dict(m=m,world=world,kind="Cstar_effective_B_minus_Q",a=a,gamma=gamma,convention="physical_pole_null",**eff))
                        updates=((4,r),(-4,t))
                        q00=4*(c[0]*c[0]).real
                    else:updates=();q00=0.
                    corner=float(part["H"][0,0]+p[0]**2-.9*part["B"][0,0]+q00)
                    for convention,restriction in (("physical_pole_null",primary),("literal_normalized_p_perp",literal)):
                        val,y=extremum(weak,restriction,which="SA",updates=updates)
                        z=s*y
                        row=dict(m=m,world=world,kind="weak_u_0.9_min",a=a,gamma=gamma,convention=convention,
                                 corner=corner,corner_fires=corner<0,detector_fires=val["value"]<THRESHOLD,
                                 p_dot_physical_z=float(p@z),W_norm_squared=float(np.dot(z*part["W"],z)),**val)
                        key=f"a{a}_gamma{gamma}_{convention}"
                        initial=16 if gamma in (0,14) else 21
                        if key not in firsts and m==initial:
                            if row["detector_fires"]:
                                name=f"m{m}_a{a.replace('/','_')}_gamma{gamma}_{convention}.npz"
                                np.savez(vectordir/name,physical_z=z,normalized_y=y,p=p,W=part["W"],omega=part["omega"])
                                firsts[key]={"first_m":m,"is_first_admitted":True,"vector":f"weak_vectors/{name}","value":val["value"],"high_precision_confirmation":"PENDING_PARENT"}
                            else:
                                firsts[key]={"initial_m":m,"initial_trigger":False,"status":"NEEDS_CONSECUTIVE_INTEGER_PREFIX","value":val["value"]}
                        rows.append(row)
                del weak,base,part
            processed.append(m)
            checkpoint()
            print(json.dumps({"m":m,"rows":len(rows),"cpu_seconds":time.process_time()-cpu}),flush=True)
        except Exception as e:
            failures.append({"m":m,"error":type(e).__name__,"message":str(e)})
            checkpoint();raise
    checkpoint()


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--budget",type=float,default=300)
    parser.add_argument("--grid",type=int,nargs="*")
    run(parser.parse_args())
