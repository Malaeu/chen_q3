"""Selected stored roots replayed through an independent entire transform."""
from pathlib import Path
import json,argparse,hashlib
import mpmath as mp

P=Path(__file__).resolve().parent;BASE=P.parent
mp.mp.dps=100
def vector_path(raw,expected_sha256):
    original=Path(raw);resolved=original if original.is_file() else BASE/'spectra/vectors'/original.name
    if not resolved.is_file():raise FileNotFoundError('Stored vector unavailable, including packet-relative basename fallback: '+str(raw))
    if hashlib.sha256(resolved.read_bytes()).hexdigest()!=expected_sha256:raise ValueError('Stored vector SHA256 mismatch: '+str(resolved))
    return resolved
def sinc(z):return mp.sin(z)/z if z else mp.mpf(1)
def sincprime(z):return (z*mp.cos(z)-mp.sin(z))/(z*z) if z else mp.mpf(0)
def transform(v,L,z,parity,derivative=False):
    b=L/2;om=2*mp.pi/L;S=sincprime if derivative else sinc
    if parity=='even':
        result=mp.sqrt(L)*v[0]*S(z*b)
        result+=mp.sqrt(2/L)*b*mp.fsum(v[n]*(-1)**n*(S((z-n*om)*b)+S((z+n*om)*b)) for n in range(1,len(v)))
    else:
        result=mp.sqrt(2/L)*b*mp.fsum(v[n-1]*(-1)**n*(S((z-n*om)*b)-S((z+n*om)*b)) for n in range(1,len(v)+1))
    return result*b if derivative else result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--ms',type=int,nargs='+',default=[16,40,80,160,300]);a=ap.parse_args()
    rows=[];continuations=[]
    for p in sorted((BASE/'roots/results').glob('*_m*.json')):
        d=json.loads(p.read_text());m=d.get('m');w=d.get('world');par=d.get('parity')
        if m not in a.ms or w not in ['zeta','dh','plant']:continue
        src=json.loads(vector_path(d['source_vector_path'],d['source_vector_sha256']).read_text());mp.mp.dps=max(100,int(src['precision_dps'])+20)
        v=list(map(mp.mpf,src['v_even0' if par=='even' else 'v_odd0']));L=mp.log(m);om=2*mp.pi/L
        for n in [0,m//2,m,m+1]:
            expected=mp.mpf(0)
            if n==0 and par=='even':expected=mp.sqrt(L)*v[0]
            elif 1<=n<=m:expected=(-1)**n*mp.sqrt(L/2)*v[n if par=='even' else n-1]
            val=transform(v,L,n*om,par)
            assert abs(val-expected)<mp.mpf('1e-85')
            continuations.append(dict(m=m,world=w,parity=par,harmonic=n,error=mp.nstr(abs(val-expected),35)))
        T=mp.mpf(d['cutoffs']['fixed_c1_4']['T'])
        candidates=[r for r in d['roots'] if r['kind'].startswith('polynomial') and 0<mp.mpf(r['z_re'])<T and abs(mp.mpf(r['z_im']))<mp.mpf('.5')]
        if not candidates:continue
        for i in sorted({0,len(candidates)//2,len(candidates)-1}):
            r=candidates[i];z=mp.mpc(r['z_re'],r['z_im']);val=transform(v,L,z,par);der=transform(v,L,z,par,True)
            correction=abs(val/der) if der else mp.inf
            assert correction<mp.mpf('1e-35')
            rows.append(dict(m=m,world=w,parity=par,root_id=r['root_id'],root_re=r['z_re'],root_im=r['z_im'],direct_residual=mp.nstr(abs(val),40),abs_derivative=mp.nstr(abs(der),40),newton_position_correction=mp.nstr(correction,40)))
    result=dict(status='PASS_SELECTED_STORED_ROOT_REPLAY',ms_requested=a.ms,samples=len(rows),harmonic_samples=len(continuations),
                max_newton_position_correction=mp.nstr(max(mp.mpf(r['newton_position_correction']) for r in rows),40) if rows else None,
                root_samples=rows,harmonic_samples_detail=continuations,
                scope='Independent sinc continuation and analytic derivative at selected stored physical roots; Newton correction is diagnostic, not a root/source eigenvector error bound.')
    (P/'transform_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if not isinstance(v,list)},indent=2))

if __name__=='__main__':main()
