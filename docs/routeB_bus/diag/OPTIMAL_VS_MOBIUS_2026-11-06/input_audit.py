# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Verify source blobs and distinguish full-Gram coefficients from R8 witnesses."""
import csv, json, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])
def main():
    pins=json.loads((HERE/"SOURCES.json").read_text())
    for pin in pins:
        assert git("rev-parse",pin["commit"]+":"+pin["path"]).decode().strip()==pin["blob"]
    pin=next(x for x in pins if x["role"]=="coefficients")
    source_bytes=git("show",pin["commit"]+":"+pin["path"])
    assert (ROOT/pin["path"]).read_bytes()==source_bytes
    source=source_bytes.decode()
    rows=list(csv.DictReader(source.splitlines()))
    results={"source_blobs_verified":len(pins),"certificate_role":"R8 upper-envelope witnesses are not substituted for full-Gram optimal vectors", "vectors":[]}
    for N in [500,1000,2000,5000]:
        rs=[r for r in rows if int(r["N"])==N]
        assert [int(r["n"]) for r in rs]==list(range(2,N+1))
        item={"N":N,"free_coefficients":len(rs)}
        if N<=2000:
            path=f"docs/routeB_bus/diag/R8_CERTIFICATE_AND_CORE_2026-11-06/certificate_witness_N{N}.json"
            w=json.loads(git("show","a180142f:"+path))
            candidate=[float.fromhex(x) for x in w["candidate_a_float_hex"]]
            assert len(candidate)==N-1
            item["max_abs_difference_R8_candidate_vs_full_Gram_optimum"]=max(abs(a+float(r["c"])) for a,r in zip(candidate,rs))
        results["vectors"].append(item)
    (HERE/"input_audit.json").write_text(json.dumps(results,indent=2)+"\n")
    print("[##############################] 100% ETA 0s input source audit PASS",flush=True)
if __name__=="__main__":main()
