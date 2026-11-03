"""Only an arithmetic-kernel probe; no producer or stored root is changed."""
from pathlib import Path
import sys,json,time
import mpmath as mp
P=Path(__file__).resolve().parents[1];sys.path.insert(0,str(P/'roots'))
from census import rational_fourier
def measure(source,coordinates):
    start=time.process_time();mp.mp.dps=720;L=mp.mpf(source['L_low']);coeff=list(map(mp.mpf,coordinates));m=source['m']
    T=(1+(1+mp.log(L))/(4*L))*2*mp.pi*m/L
    data=json.loads((P/'roots/results'/f'zeta_even_m{m}.json').read_text());shifts=[]
    for r in data['roots']:
        z=mp.mpc(r['z_re'],r['z_im'])
        if not(r['kind'].startswith('polynomial') and 0<mp.re(z)<T and abs(mp.im(z))<mp.mpf('.5')):continue
        f,fp=rational_fourier(coeff,z,L,'even',True);shift=abs(f/fp);shifts.append(shift)
    maximum=max(shifts);assert maximum<mp.mpf('1e-60'),maximum
    return dict(scope='First Newton corrections at all stored HIGH primary-strip roots, not a new complete isolation.',roots=len(shifts),max_correction=mp.nstr(maximum,40),CPU_seconds=time.process_time()-start)
