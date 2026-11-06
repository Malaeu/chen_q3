# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.9.0"]
# ///
"""Independent explicit Fourier-tail bound using compact BV truncations, Arb128."""
import csv,json,math,time,subprocess,hashlib
from pathlib import Path
from flint import arb,ctx
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
SOURCE='docs/routeB_bus/diag/NB_RATE_THERMOMETER_2026-11-06/part_a_coefficients.csv'
SOURCE_COMMIT='ba5654b46adf84159702748b006699bafa0ed89b'
SOURCE_BLOB='7baa38bc0f5a9437e985f739aecb823ec2dedf1a'
KS=[16,64,256,1024,4096,16384,65536]
def upper(x):
    return math.nextafter(float(x.upper()),math.inf)
def main():
    ctx.prec=128;start=time.monotonic()
    source=subprocess.check_output(['git','-C',str(ROOT),'show',SOURCE_COMMIT+':'+SOURCE])
    blob=subprocess.check_output(['git','hash-object','--stdin'],input=source,text=False).decode().strip()
    assert blob==SOURCE_BLOB
    rows=list(csv.DictReader(source.decode().splitlines()))
    for N in [500,1000,2000,5000]:
        assert [int(r['n']) for r in rows if int(r['N'])==N]==list(range(2,N+1))
    mu=[1]*5001;mu[0]=0;prime=[True]*5001
    for p in range(2,5001):
        if prime[p]:
            for k in range(p,5001,p):mu[k]*=-1
            for k in range(p*p,5001,p):prime[k]=False
            for k in range(p*p,5001,p*p):mu[k]=0
    output={'source_commit':SOURCE_COMMIT,'source_blob':SOURCE_BLOB,'source_sha256':hashlib.sha256(source).hexdigest(),'precision_bits':128,'T':1000,'method':'BV truncation plus L2 remainder; independent of discrete Gram error and quadrature','input_convention':'opt uses exact binary64 parsed CSV values; taper uses Arb transcendental enclosure','rows':[]}
    invsqrt=[arb(0)]+[1/arb(k).sqrt() for k in range(1,max(KS)+1)]
    for N in [500,1000,2000,5000]:
        opt={int(r['n']):-arb(float(r['c'])) for r in rows if int(r['N'])==N}
        for kind,c in [('opt',opt),('taper',{n:mu[n]*(1-arb(n).log()/arb(N).log()) for n in range(2,N+1)})]:
            B=1+sum((abs(v) for v in c.values()),arb(0));s=sum((v/n for n,v in c.items()),arb(0))
            jumps=[arb(s) for _ in range(max(KS))]
            for n,v in c.items():
                for k in range(n,max(KS),n):jumps[k]-=v
            residual=[arb(1)]
            for k in range(1,max(KS)):residual.append(residual[-1]+jumps[k])
            variation=abs(residual[1]); bounds=[]
            for k in range(1,max(KS)):
                variation+=abs(residual[k])*(invsqrt[k]-invsqrt[k+1])
                if k>=2:variation+=abs(jumps[k])*invsqrt[k]
                K=k+1
                if K in KS:
                    V=variation+abs(residual[k])*invsqrt[K]
                    bound=(V/(arb.pi()*1000).sqrt()+B*invsqrt[K])**2
                    bounds.append({'K':K,'B_upper':upper(B),'V_upper':upper(V),'tail_upper':upper(bound),'tail_ball':str(bound)})
            best=min(bounds,key=lambda r:r['tail_upper'])
            output['rows'].append({'N':N,'kind':kind,'best':best,'all_K':bounds})
            done=len(output['rows']);elapsed=time.monotonic()-start
            print(f"[{'#'*done}{'.'*(8-done)}] {100*done/8:.1f}% ETA {elapsed*(8-done)/done:.1f}s N={N} {kind} tail<={best['tail_upper']:.9g}",flush=True)
    (HERE/'tail_bound.json').write_text(json.dumps(output,indent=2)+'\n')
if __name__=='__main__':main()
