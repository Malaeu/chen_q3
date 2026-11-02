"""Compare full independent precision repeats and source-control witnesses."""
from pathlib import Path
import json,csv
import mpmath as mp
P=Path(__file__).resolve().parent; mp.mp.dps=170
rows=[]
for world in ['true_zeta','half_atoms','three_halves_atoms','smooth_atoms']:
    a=list(csv.DictReader((P/'controls'/f'{world}_mesh64_dps100.csv').open()))
    b=list(csv.DictReader((P/'controls'/f'{world}_mesh64_dps160.csv').open()))
    err=max(abs(mp.mpf(x['sigma2'])-mp.mpf(y['sigma2']))/abs(mp.mpf(y['sigma2'])) for x,y in zip(a,b))
    assert len(a)==len(b)==384
    assert all(x['negative_pivots']==y['negative_pivots'] for x,y in zip(a,b))
    assert err<mp.mpf('1e-50')
    r=json.loads((P/'controls'/f'{world}_mesh64_dps160.json').read_text())
    witness=r['witness']
    if witness:
        assert mp.mpf(witness['direct'])<0
        assert mp.mpf(witness['relative_error'])<mp.mpf('1e-130')
    rows.append(dict(world=world,rows=len(a),max_relative_change=mp.nstr(err,20),all_negative_indices_match=True,first_negative_t=r['first_negative_t'],direct_witness_relative_error=witness['relative_error'] if witness else None))
# Independent quadrature for the exact smooth-control expression.
smooth=[]
for t in [mp.mpf('.75'),mp.mpf('1'),mp.mpf('3'),mp.mpf('6')]:
    aa=mp.log(2)
    q=mp.quad(lambda s:mp.exp(s/2)*(t-s),[aa,t])
    formula=4*mp.exp(t/2)-(2*t+4-2*aa)*mp.exp(aa/2)
    smooth.append(mp.nstr(abs(q-formula),20))
    assert abs(q-formula)<mp.mpf('1e-160')
(P/'controls'/'VALIDATION.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',precision=rows,smooth_integral_absolute_errors=smooth),indent=2)+'\n')
print(json.dumps(rows,indent=2))
