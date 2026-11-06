# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Validate the numerical interface between fitted profiles and proof objects."""
import csv,json,math
from pathlib import Path
import numpy as np
H=Path(__file__).resolve().parent
def main():
    profiles={k:v['bestprofile'] for k,v in json.loads((H/'selected_profiles.json').read_text()).items()}
    rows=list(csv.DictReader((H/'selected_vectors.csv').open()))
    mu=np.ones(10001,dtype=int);mu[0]=0;prime=np.ones(10001,dtype=bool)
    for p in range(2,10001):
        if prime[p]:
            mu[p::p]*=-1;mu[p*p::p*p]=0;prime[p*p::p]=False
    maxerr=0.;logerr=0.;checked=0
    for key,profile in profiles.items():
        N=int(key);rs=[r for r in rows if int(r['N'])==N];assert [int(r['n']) for r in rs]==list(range(1,N+1))
        assert float(rs[0]['best'])==float(rs[0]['log'])==1
        n=np.arange(2,N+1);x=np.log(N/n)/math.log(N)
        if profile['kind']=='polynomial':
            P=sum(float(c)*x**j for j,c in enumerate(profile['monomialcoeffs'],1))
        else:
            c=profile['basiscoeffs'];z=float(profile['x0']);u=np.maximum(z-x,0)
            P=float(c['x'])*x+float(c['(x0-x)_+^2-x0^2'])*(u*u-z*z)+float(c['(x0-x)_+^3-x0^3'])*(u**3-z**3)
        expected=mu[n]*P;actual=np.array([float(r['best']) for r in rs[1:]])
        maxerr=max(maxerr,float(np.max(abs(expected-actual))))
        logerr=max(logerr,float(np.max(abs(mu[n]*x-np.array([float(r['log']) for r in rs[1:]])))))
        assert np.all(actual[mu[n]==0]==0)
        checked+=len(rs)
    assert maxerr<1e-10 and logerr<1e-12
    allfits=list(csv.DictReader((H/'fit_all.csv').open()))
    nesting=[]
    for N in map(int,profiles):
        rr={r['family']:float(r['E']) for r in allfits if int(r['N'])==N}
        for d in range(1,5):
            assert rr[f'poly_d{d}_free']<=rr[f'poly_d{d}_fixed1']+1e-10
            if d>1:
                for endpoint in ['free','fixed1']:assert rr[f'poly_d{d}_{endpoint}']<=rr[f'poly_d{d-1}_{endpoint}']+1e-10
        candidates=[v for k,v in rr.items() if (k.startswith('poly_') and not k.startswith('poly_d4')) or k.startswith('spline_')]
        assert abs(float(profiles[str(N)]['E'])-min(candidates))<2e-12
    result={'status':'PASS','N_count':len(profiles),'vector_rows':checked,'max_abs_profile_vector_difference':maxerr,'max_abs_log_vector_difference':logerr,'nested_minima_and_selected_family_checks':'PASS at all target N','raw_a1':'exactly1; all non-squarefree free coefficients exactly0'}
    (H/'OUTPUT_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print('[##############################] 100% ETA 0s selected profile/vector interface PASS')
if __name__=='__main__':main()
