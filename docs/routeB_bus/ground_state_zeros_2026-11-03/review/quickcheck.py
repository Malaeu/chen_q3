"""Independent algebra/input checks; never an eigenproblem or certificate."""
from pathlib import Path
import json, hashlib
import mpmath as mp

P=Path(__file__).resolve().parent
BASE=P.parent
mp.mp.dps=90

def F(v,L,t):
    b=L/2;w=2*mp.pi/L
    return mp.fsum(vn*(1 if n==0 else mp.sqrt(2))*(-1)**n*b/mp.sqrt(L)
                   *(mp.sinc((t-n*w)*b)+mp.sinc((t+n*w)*b))
                   for n,vn in enumerate(v))

def rational(v,L,t):
    w=2*mp.pi/L
    return 2*t*mp.sin(t*L/2)/mp.sqrt(L)*mp.fsum(
        vn*(1 if n==0 else mp.sqrt(2))/(t*t-(n*w)**2)
        for n,vn in enumerate(v))

def main():
    L=mp.log(16);w=2*mp.pi/L
    v=[mp.mpf(1),mp.mpf(2),mp.mpf(-3),mp.mpf(4)]
    v=[x/mp.sqrt(mp.fsum(x*x for x in v)) for x in v]
    diffs=[abs(F(v,L,t)-rational(v,L,t)) for t in [mp.mpf('.731'),mp.mpc('1.137','.317'),mp.mpc('5.1','-.25')]]
    continuation=[abs(F(v,L,n*w)-((-1)**n*mp.sqrt(L/(1 if n==0 else 2))*v[n])) for n in range(len(v))]
    exterior=[abs(F(v,L,n*w)) for n in [4,5,11]]
    e0=[mp.mpf(1),mp.mpf(0),mp.mpf(0),mp.mpf(0)]
    e0_internal=[abs(F(e0,L,n*w)) for n in [1,2,3]]
    assert max(diffs+continuation+exterior+e0_internal)<mp.mpf('1e-85')
    assert all(abs(F(v,L,n*w))>mp.mpf('.1') for n in range(len(v)))
    p=BASE/'inputs/dh_zeros_900_200dps.json';d=json.loads(p.read_text())
    line=d['critical_line_zeros'];pairs=d['off_line_pairs'];allroots=d['upper_half_plane_zeros']
    lookup={(r['sigma'],r['gamma']) for r in allroots}
    assert len(lookup)==len(allroots)==len(line)+2*len(pairs)==798
    assert all((r['sigma'],r['gamma']) in lookup for r in line)
    assert all((r[k],r['gamma']) in lookup for r in pairs for k in ['sigma_left','sigma_right'])
    symmetry=max(abs(mp.mpf(r['sigma_right'])+mp.mpf(r['sigma_left'])-1) for r in pairs)
    assert symmetry<mp.mpf('1e-85')
    assert all(0<mp.mpf(r['sigma_left'])<mp.mpf('.5')<mp.mpf(r['sigma_right'])<1 for r in pairs)
    result=dict(status='BOUNDED_REVIEW_CHECKS_PASS_NUMERICAL_NOT_CERTIFICATE',
                direct_rational_identity_max_error=str(max(diffs)),
                internal_harmonic_continuation_max_error=str(max(continuation)),
                exterior_harmonic_max_residual=str(max(exterior)),
                e0_internal_harmonics_are_zeros_max_residual=str(max(e0_internal)),
                all_generic_internal_harmonics_nonzero=True,
                dh_line_count=len(line),dh_quartet_count=len(pairs),
                dh_positive_height_offline_count=2*len(pairs),dh_total_count=len(allroots),
                dh_all_saved_coordinates_distinct=True,dh_pair_symmetry_max_error=str(symmetry),
                dh_all_listed_pairs_inside_open_critical_strip=True,
                dh_file_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),dps=mp.mp.dps)
    (P/'quickfindings.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
