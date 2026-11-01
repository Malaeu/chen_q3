"""Summarize and cross-check the heat-temperature numerical canary."""
from heat_fit import *

def polyadd(a,b):
    r=[mp.mpf(0)]*max(len(a),len(b))
    for i,x in enumerate(a):r[i]+=x
    for i,x in enumerate(b):r[i]+=x
    return r
def polymul(a,b):
    r=[mp.mpf(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):r[i+j]+=x*y
    return r
def derivative(a):return [i*a[i] for i in range(1,len(a))]

def main():
    mp.mp.dps=100
    main=json.loads((OUT/'main_results.json').read_text())
    validation=json.loads((OUT/'validation_results.json').read_text())
    checks=[]
    for r in validation['results']:
        q=next(x for x in main['results'] if x['m']==r['m'] and x['family']==r['family'])
        v=mp.matrix(r['projected_vector']);v0=mp.matrix(q['projected_vector'])
        checks.append(dict(m=r['m'],family=r['family'],s_absolute_change=fmt(abs(mp.mpf(r['s'])-mp.mpf(q['s']))),
                           residual_squared_absolute_change=fmt(abs(mp.mpf(r['residual_squared'])-mp.mpf(q['residual_squared']))),
                           energy_relative_change=fmt(abs(mp.mpf(r['energy'])/mp.mpf(q['energy'])-1)),
                           vector_relative_change=fmt(mp.norm(v-v0)/mp.norm(v))))
    csvout('validation_comparison.csv',checks)
    tails=[]
    for r in main['results']:
        if r['family']!='heat':continue
        d=source(r['m']);s=mp.mpf(r['s']);T=mp.mpf(main['T']);v=mp.matrix(r['projected_vector'])
        # |H(t)|<=H(0) by positivity of h; |B_n(t)|<=sqrt(L) by Cauchy-Schwarz.
        delta=mp.sqrt(d['m']+1)*H(0)*mp.sqrt(d['L'])*mp.exp(-s*T*T)/(2*mp.pi*s*T)
        eprice=4*mp.norm(d['A'])*delta/mp.norm(v) # Frobenius bounds operator norm.
        tails.append(dict(m=d['m'],s=fmt(s),T=fmt(T),coefficient_vector_tail_upper=fmt(delta),
                          rayleigh_tail_error_upper=fmt(eprice),relative_to_energy=fmt(eprice/mp.mpf(r['energy'])),
                          scope='Fourier truncation only; quadrature error checked separately, not interval-certified'))
    csvout('fourier_tail_bounds.csv',tails)
    polynomial=[]
    for m in (8,12,16,20,24):
        d=source(m);vv=[d['h'],d['h2'],d['h4']/2]
        a=[mp.fdot(d['f'],v) for v in vv];b=[mp.mpf(0)]*5
        for i in range(3):
            for j in range(3):b[i+j]+=mp.fdot(vv[i],vv[j])
        g=polyadd(polymul(derivative(a),b),[-x/2 for x in polymul(a,derivative(b))])
        # The degree-five term cancels identically; eliminate roundoff there.
        g=g[:5]
        roots=mp.polyroots(list(reversed(g)),maxsteps=1000,error=False,extraprec=100)
        candidates=[mp.mpf(0)]+[mp.re(r) for r in roots if abs(mp.im(r))<mp.mpf('1e-70') and mp.re(r)>0]
        # Roots of a(s) give W=0, so cannot beat the displayed positive overlap.
        rr=[(measures(d,poly_vectors(d,s)[0]),s) for s in candidates]
        best=min(rr,key=lambda r:mp.mpf(r[0]['residual_squared']))
        row=next(r for r in main['results'] if r['m']==m and r['family']=='quadratic')
        polynomial.append(dict(m=m,stationary_polynomial_coefficients_ascending=[fmt(x) for x in g],
            roots=[str(r) for r in roots],nonnegative_candidates=[fmt(x) for x in candidates],
            best_s=fmt(best[1]),s_difference_from_fit=fmt(abs(best[1]-mp.mpf(row['s']))),
            infinite_s_residual_squared=measures(d,d['h4'])['residual_squared']))
    (OUT/'polynomial_global_check.json').write_text(json.dumps(polynomial,indent=2)+'\n')
    normcheck=max(abs(mp.mpf(r['w'])+mp.mpf(r['residual_squared'])-1) for r in main['results'])
    (OUT/'validation_summary.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',
        source_commit='167dff63a632f170fed2d01d88af61268ad0af7f',
        comparison_significant_digits=80,zero_difference_meaning='agreement at saved precision, not exact equality',
        precision_and_quadrature='100dps GL40 panels width4 T256 to140dps GL56 width4 T320, m8 andm24; higherprecision source matrices/eigenvectors',
        max_w_plus_residual_minus_one=fmt(normcheck),comparisons=checks,
        fitted_s_monotone_increasing=False,fitted_s_monotone_decreasing=False,
        observation='Both families increase through m20 and slightly decrease at m24; no measured decay to zero.'),indent=2)+'\n')
    print(json.dumps(checks,indent=2))

if __name__=='__main__':main()
