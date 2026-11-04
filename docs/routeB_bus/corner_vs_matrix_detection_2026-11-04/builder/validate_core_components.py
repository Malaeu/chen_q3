"""Fresh MPFR decomposition checks, then both-world assembly benchmarks only."""
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import sys
import time
import numpy as np
import core_components as core
import source_float

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,'/workspace/conditioning_deps')
import gmpy2 as g
import flint


def mp_components(old,m,out,bits):
    g.get_context().precision=bits+40
    f=g.mpfr;zero=f(0);pi=g.const_pi();L=g.log(m)
    ze,dh=old.coefficients(max(300,m),bits)
    ds=[f(1)]+[g.sqrt(2)]*m
    worlds={}
    for world,b in [('zeta',ze),('dh',dh)]:
        weights=[b[k]/g.sqrt(k) for k in range(2,m)]
        ratios=[g.log(k)/L for k in range(2,m)]
        ps=[];pd=[]
        for n in range(m+1):
            sn=[g.sin(2*pi*n*r) for r in ratios]
            co=[g.cos(2*pi*n*r) for r in ratios]
            ps.append(sum((w*s for w,s in zip(weights,sn)),zero))
            pd.append(sum((w*(2*(1-r)*c-(s/(pi*n) if n else zero)) for w,r,c,s in zip(weights,ratios,co,sn)),zero))
        B=np.empty((m+1,m+1),dtype=object)
        for i in range(m+1):
            B[i,i]=pd[i]
            for j in range(i+1,m+1):
                B[i,j]=B[j,i]=-ds[i]*ds[j]/pi*(i*ps[i]-j*ps[j])/(i*i-j*j)
        p=np.zeros(m+1,dtype=object)
        if world=='zeta':
            p=np.array([g.sqrt(2/L)*ds[j]*g.sinh(L/4)/((2*pi*j/L)**2+f('.25')) for j in range(m+1)],dtype=object)
        H=out[world][0]+B-np.outer(p,p)
        worlds[world]=dict(H=np.asarray(H,float),B=np.asarray(B,float),p=np.asarray(p,float),
                           A=np.asarray(out[world][0],float),coefficients=np.asarray(b[:m],float),
                           pole_squared_norm=float(sum((x*x for x in p),zero)))
    return worlds


def run():
    start=time.process_time();source_float.verify_source();core.verify_sources()
    initial_old_hash=hashlib.sha256(Path(source_float.__file__).read_bytes()).hexdigest()
    rayleigh_path=ROOT/'rayleigh_pinned.py';rayleigh_hash=hashlib.sha256(rayleigh_path.read_bytes()).hexdigest()
    comparisons=[]
    for m in [80,160]:
        # New module per m, and a new actual original build, not a stored matrix.
        spec=importlib.util.spec_from_file_location('_pinned_fresh',source_float.SOURCE_PATH)
        old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
        cpu=time.process_time();out,source_meta=old.build(m,256)
        mp=mp_components(old,m,out,256)
        reference_cpu=time.process_time()-cpu
        for world in ['zeta','dh']:
            parts,meta=core.build(m,world)
            row=dict(m=m,world=world,bits=256,source_meta=source_meta,reference_cpu_seconds=reference_cpu,
                     core_meta=meta,
                     max_component_errors={k:float(np.max(np.abs(parts[k]-mp[world][k]))) for k in ['H','B','p','A','coefficients']},
                     reconstruction_error=float(np.max(np.abs(parts['A']-(parts['H']+np.outer(parts['p'],parts['p'])-parts['B'])))),
                     symmetry_errors={k:float(np.max(np.abs(parts[k]-parts[k].T))) for k in ['H','B','A']},
                     pole_squared_norm=float(parts['p']@parts['p']),
                     mp_pole_squared_norm=mp[world]['pole_squared_norm'],
                     corner_component_errors={k:float(abs(core.corner(m,world)[k]-v)) for k,v in [('H00',parts['H'][0,0]),('B00',parts['B'][0,0]),('p0',parts['p'][0]),('A00',parts['A'][0,0])]},
                     W_error=float(np.max(np.abs(parts['W']-(1+parts['omega']**2)))))
            if world=='zeta':
                A0,oldmeta=source_float.build(m)
                row['unchanged_source_float_A_error']=float(np.max(np.abs(parts['A']-A0)))
            else:
                tau=(g.sqrt(10-2*g.sqrt(5))-2)/(g.sqrt(5)-1)
                expected=(1+tau*tau)*g.log(6)
                row['dh_b6']=str(parts['coefficients'][6]);row['dh_b6_expected_mp']=str(expected)
                row['dh_b6_error']=float(abs(g.mpfr(str(parts['coefficients'][6]))-expected))
                row['dh_p_identically_zero']=bool(np.all(parts['p']==0))
            comparisons.append(row)
            (ROOT/'core_component_comparisons.json').write_text(json.dumps(comparisons,indent=2)+'\n')
            print(json.dumps(row),flush=True)
            if any(v>1e-12 for v in row['max_component_errors'].values()):raise RuntimeError('MP_COMPONENT_GATE_FAILED')
            if any(v!=0 for v in row['symmetry_errors'].values()):raise RuntimeError('EXACT_SYMMETRY_GATE_FAILED')
            if row['reconstruction_error']>1e-12 or any(v>1e-12 for v in row['corner_component_errors'].values()):raise RuntimeError('RECONSTRUCTION_GATE_FAILED')
            if world=='zeta' and row['unchanged_source_float_A_error']>1e-12:raise RuntimeError('OLD_FLOAT_RECONSTRUCTION_FAILED')
            if world=='dh' and (row['dh_b6_error']>1e-12 or not row['dh_p_identically_zero']):raise RuntimeError('DH_SOURCE_GATE_FAILED')
        del out,mp,parts
    benchmarks=[]
    for world in ['zeta','dh']:
        parts,meta=core.build(3000,world)
        row=dict(m=3000,world=world,core_meta=meta,
                 reconstruction_error=float(np.max(np.abs(parts['A']-(parts['H']+np.outer(parts['p'],parts['p'])-parts['B'])))),
                 maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                 pole_squared_norm=float(parts['p']@parts['p']),
                 symmetric=all(np.array_equal(parts[k],parts[k].T) for k in ['H','B','A']),
                 finite=all(np.all(np.isfinite(parts[k])) for k in ['H','B','p','A']))
        benchmarks.append(row);print(json.dumps(row),flush=True)
        if not row['symmetric'] or not row['finite']:raise RuntimeError('BENCHMARK_COMPONENT_GATE_FAILED')
        del parts
    report=dict(comparisons=comparisons,benchmarks=benchmarks,
                total_cpu_seconds=time.process_time()-start,budget_cpu_seconds=180,blas_threads=1,
                versions=dict(gmpy2=g.version(),flint=flint.__version__),
                source_float_before_sha256=initial_old_hash,
                source_float_after_sha256=hashlib.sha256(Path(source_float.__file__).read_bytes()).hexdigest(),
                rayleigh_pinned_before_sha256=rayleigh_hash,
                rayleigh_pinned_after_sha256=hashlib.sha256(rayleigh_path.read_bytes()).hexdigest(),
                detector_runs=0,planted_runs=0,
                honesty='DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER_NOT_RH')
    (ROOT/'core_component_validation.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':run()
