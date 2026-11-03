import sys,time,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent));from census import numerator
from flint import ctx,arb
p=Path(__file__).resolve().parents[1]/'spectra/vectors/zeta_m160.json';x=json.loads(p.read_text());P=numerator(x['c'],'even',160,1300)
for startbits in [80,160,1300]:
 ctx.prec=startbits;t=time.monotonic();rr=P.roots(tol=arb('1e-165'),maxprec=5000);print(startbits,len(rr),time.monotonic()-t,rr[10].real.rad().str(10),flush=True)
