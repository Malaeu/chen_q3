"""Fresh pinned-source comparisons, then bounded unplanted benchmarks.
Run with OPENBLAS_NUM_THREADS=2 OMP_NUM_THREADS=2. Never runs a plant.
"""
import importlib.util
import json
from pathlib import Path
import resource
import time
import numpy as np
from scipy.linalg import eigvalsh
import source_float as sf

ROOT = Path(__file__).resolve().parent

def run():
    all_start = time.process_time()
    sf.verify_source()
    spec=importlib.util.spec_from_file_location('pinned',sf.SOURCE_PATH)
    old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
    comparisons=[]
    for m in [80,160,300]:
        start=time.process_time()
        out, original_meta = old.build(m,256)
        source_cpu=time.process_time()-start
        A, meta=sf.build(m)
        B=np.asarray(out['zeta'][0],dtype=np.float64)
        D=A-B
        row=dict(m=m,bits=256,decimal_digits=256*np.log10(2),source_cpu_seconds=source_cpu,
                 source_meta=original_meta,builder_meta=meta,
                 max_entry_error=float(np.max(np.abs(D))),frobenius_error=float(np.linalg.norm(D)),
                 operator_error=float(np.max(np.abs(eigvalsh(D)))),
                 float_lambda_min=float(eigvalsh(A,subset_by_index=[0,0])[0]),
                 source_rounded_lambda_min=float(eigvalsh(B,subset_by_index=[0,0])[0]))
        comparisons.append(row)
        (ROOT/'validation_comparisons.json').write_text(json.dumps(comparisons,indent=2)+'\n')
        print(json.dumps(row),flush=True)
        if row['max_entry_error']>1e-12 or row['float_lambda_min'] < -1e-12:
            raise RuntimeError(f'SOURCE_COMPARISON_CONTROL_FAILED_m{m}')
        del out,A,B,D
    benchmarks=[]
    for m in [300,1000,3000]:
        A,meta=sf.build(m)
        start=time.perf_counter();cpu=time.process_time()
        low=float(eigvalsh(A,subset_by_index=[0,0],check_finite=False,overwrite_a=False)[0])
        row=dict(m=m,builder_meta=meta,lambda_min=low,
                 eig_wall_seconds=time.perf_counter()-start,eig_cpu_seconds=time.process_time()-cpu,
                 maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                 unplanted_control_pass=low>=-1e-12)
        benchmarks.append(row)
        report=dict(comparisons=comparisons,benchmarks=benchmarks,
                    total_cpu_seconds=time.process_time()-all_start, planted_runs=0,
                    initial_budget_cpu_seconds=180,blas_threads=2)
        (ROOT/'validation_report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(row),flush=True)
        del A
    return report

if __name__=='__main__':run()
