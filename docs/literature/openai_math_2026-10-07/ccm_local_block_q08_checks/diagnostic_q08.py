"""Original four-mode kernel identities, not spectral certificates.
Run: python3 diagnostic_q08.py (mpmath required). No path substitutions.
No large prime sum, zeta zero, or full CCM spectrum is evaluated.
"""
from pathlib import Path
import hashlib,json
import mpmath as mp
mp.mp.dps=65
L=mp.mpf(512)*mp.log(2); M=256; w=2*mp.pi/L
v=(-1,3,-3,1)
def a(j):return mp.mpf(1)/4+(w*j)**2
def col(j,t):return -sum(v[r]*a(j+r)*mp.exp(1j*w*(j+r)*t) for r in range(4))/mp.sqrt(L)
def Q(j,k,s):
    if j==k:return 2*(1-s/L)*mp.cos(w*j*s)
    return (mp.sin(w*k*s)-mp.sin(w*j*s))/(mp.pi*(j-k))
rows=[]
for j,k,frac in ((-2,1,mp.mpf('0.21')),(-3,-1,mp.mpf('0.5')),(0,2,mp.mpf('0.91'))):
    s=frac*L
    mixed=sum(v[r]*v[t]*a(j+r)*a(k+t)*Q(j+r,k+t,s) for r in range(4) for t in range(4))
    knots=[(L-s)*i/32 for i in range(33)]
    overlap=mp.quad(lambda t:mp.conj(col(j,t+s))*col(k,t)+mp.conj(col(j,t))*col(k,t+s),knots)
    err=abs(overlap-mixed)
    assert err<mp.mpf('1e-48')
    csum=sum(-v[r]*a(j+r) for r in range(4))
    pos=sum(-v[r]*a(j+r)/(mp.mpf('.5')+1j*w*(j+r)) for r in range(4))
    neg=sum(-v[r]*a(j+r)/(-mp.mpf('.5')+1j*w*(j+r)) for r in range(4))
    assert max(abs(csum),abs(pos),abs(neg))<mp.mpf('1e-55')
    rows.append({'left_start_mode':j,'right_start_mode':k,'s_over_L':str(frac),
                 'mixed_entry':str(mixed),'overlap_error':str(err),
                 'normalized_constraint_residual':str(max(abs(csum),abs(pos),abs(neg)))})
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','cases':len(rows),'decimal_digits':mp.mp.dps,
     'source_cell':'m=2^512,epsilon=1/64,M=R=256,L=512log(2)',
     'scope':'Only individual mixed kernels and original contacts. No prime spectra or asymptotic validation.',
     'rows':rows,'actual_large_prime_sums':0,'full_ccm_spectral_runs':0,'arb_runs':0,'lean_runs':0,
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('diagnostic_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
