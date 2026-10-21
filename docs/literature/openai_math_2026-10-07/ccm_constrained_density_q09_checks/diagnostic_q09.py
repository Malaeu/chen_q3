"""Q09 source-geometry checks, not interval or CCM spectral certificates.
Run: python3 diagnostic_q09.py (mpmath required).
No parameter or path substitution is needed. No dependency is installed here.
"""
from pathlib import Path
import hashlib,json
import mpmath as mp
mp.mp.dps=55
L=192*mp.log(2); M=8; K=2048; w=2*mp.pi/L
js=list(range(-M,M+1)); om=[w*j for j in js]
v=(-1,3,-3,1)
g=[mp.mpc((-1)**k*(k+1)/(k+2), (k%3-1)/(k+3)) for k in range(2*M-2)]
c=[mp.mpc(0)]*(2*M+1)
for k,gk in enumerate(g):
    for r,vr in enumerate(v):
        c[k+r]-=(mp.mpf(1)/4+om[k+r]**2)*vr*gk
norm=mp.sqrt(mp.fsum(abs(x)**2 for x in c));c=[x/norm for x in c]
assert max(abs(mp.fsum(c)),abs(mp.fsum(cj/(mp.mpf('.5')+1j*x) for cj,x in zip(c,om))),abs(mp.fsum(cj/(mp.mpf('.5')-1j*x) for cj,x in zip(c,om)))) < mp.mpf('1e-48')
ks=list(range(-K,K));nu=[w*(k+mp.mpf('.5')) for k in ks]
ucoef=[1j/mp.pi*mp.fsum(cj/(j-k-mp.mpf('.5')) for j,cj in zip(js,c)) for k in ks]
weights=[abs(z)**2 for z in ucoef]
tail=mp.mpf(8)*(2*M+1)*M*M/(3*mp.pi**2*K**3)
norm_defect=1-mp.fsum(weights)
assert -mp.mpf('1e-45')<=norm_defect<=tail
r=lambda x:1/(mp.mpf('.25')+x*x)
h_even=mp.fsum(r(x)*abs(cj)**2 for x,cj in zip(om,c))
h_half=mp.fsum(r(x)*ww for x,ww in zip(nu,weights))
h_tail=r(w*(K+mp.mpf('.5')))*tail
assert -mp.mpf('1e-45')<=h_even-h_half<=h_tail

def f(t):return mp.fsum(cj*mp.exp(1j*x*t) for x,cj in zip(om,c))/mp.sqrt(L)
u_errors=[]
for k in (-3,0,2):
    x=w*(k+mp.mpf('.5'))
    direct=mp.quad(lambda t:f(t)*mp.exp(-1j*x*t)/mp.sqrt(L),[L*a/16 for a in range(17)])
    formula=1j/mp.pi*mp.fsum(cj/(j-k-mp.mpf('.5')) for j,cj in zip(js,c))
    error=abs(direct-formula);assert error<mp.mpf('1e-45')
    u_errors.append(str(error))

def Q(j,k,s):
    if j==k:return 2*(1-s/L)*mp.cos(w*j*s)
    return (mp.sin(w*k*s)-mp.sin(w*j*s))/(mp.pi*(j-k))
rows=[]
for frac in (mp.mpf('0.15'),mp.mpf('0.37'),mp.mpf(1)):
    s=L*frac
    source=mp.fsum(mp.conj(cj)*cl*Q(j,l,s) for j,cj in zip(js,c) for l,cl in zip(js,c))
    quadrature=mp.fsum(mp.cos(x*s)*abs(cj)**2 for x,cj in zip(om,c))+mp.fsum(mp.cos(x*s)*ww for x,ww in zip(nu,weights))
    error=abs(source-quadrature)
    assert error<=tail+mp.mpf('1e-45')
    rows.append({'s_over_L':str(frac),'source_kernel_form':str(source),'truncated_two_grid_form':str(quadrature),'difference':str(error),'proved_absolute_tail_envelope_not_interval':str(tail)})
# The endpoint test would return 2, not 0, on the original grid alone.
assert abs(mp.fsum(2*mp.cos(x*L)*abs(cj)**2 for x,cj in zip(om,c))-2)<mp.mpf('1e-45')
# All tests use literal original geometry; none sums primes up to m=2^192.
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','decimal_digits':mp.mp.dps,
     'source_cell':'m=2^192,epsilon=1/64,M=R=8,N=m,L=192log(2)',
     'half_grid_cutoff_K':K,'kernel_cases':len(rows),'half_coefficient_integral_cases':len(u_errors),
     'unitarity_truncation_defect':str(norm_defect),'green_moment_truncation_defect':str(h_even-h_half),
     'green_tail_envelope':str(h_tail),'coefficient_integral_errors':u_errors,'kernel_rows':rows,
     'scope':'Original finite-band kernel and transform normalization. All bounds are PAPER bounds evaluated with noninterval mpmath; no spectral or asymptotic certificate.',
     'large_prime_sums':0,'full_ccm_spectral_runs':0,'arb_runs':0,'lean_runs':0,'independent_review':'NOT_RUN',
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('diagnostic_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
