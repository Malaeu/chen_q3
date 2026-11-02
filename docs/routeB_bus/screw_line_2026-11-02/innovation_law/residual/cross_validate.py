"""Compare independently implemented predictor scans at saved sample points."""
from residual import *
mp.mp.dps=90
budgets=list(csv.DictReader((ROOT/'budgets.csv').open()));out=[]
for row in budgets:
    core=ROOT.parent/'core'/f"{row['world']}_mesh{row['mesh']}_dps100.csv"
    vals=list(csv.DictReader(core.open()))
    other=next(x for x in vals if mp.mpf(x['t'])==mp.mpf(row['t']))
    error=abs(mp.mpf(row['sigma2'])-mp.mpf(other['sigma2']))
    assert error<mp.mpf('1e-60')
    out.append(dict(world=row['world'],mesh=row['mesh'],t=row['t'],absolute_difference=st(error),negative_index_matches=int(row['full_negative_index'])==int(other['negative_inertia'])))
assert all(x['negative_index_matches'] for x in out)
write('core_cross_validation.csv',out)
