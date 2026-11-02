"""Finalize finite resolution comparison, including boundary KKT interpretation."""
from pathlib import Path
import json,csv
import mpmath as mp
OUT=Path(__file__).resolve().parent

def read(name):return json.loads((OUT/name).read_text())
def write_csv(name,rows):
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
def vec(r,key):return mp.matrix([mp.mpf(x) for x in r[key]])
def derivative(r):return 2*mp.mpf(r['coefficient_c'])*mp.mpf(r['stationary_residual'])/mp.mpf(r['heat_projection_norm_squared'])
def main():
    mp.mp.dps=180;fmt=lambda x:mp.nstr(x,100)
    a=read('main_results.json')['results'];v=read('validation_results.json')['results'][0];r=next(x for x in a if x['window_m']==8 and x['N']==68)
    validation=dict(window_m=8,N=68,primary_dps=140,validation_dps=160,primary_matrix_order=128,validation_matrix_order=160,primary_spectral_order=56,validation_spectral_order=64,T=320,
        s_absolute_difference=fmt(abs(mp.mpf(r['s_star'])-mp.mpf(v['s_star']))),
        lambda_relative_difference=fmt(abs(mp.mpf(r['lambda0'])/mp.mpf(v['lambda0'])-1)),
        ground_vector_L2_difference=fmt(mp.norm(vec(r,'ground_even_coefficients')-vec(v,'ground_even_coefficients'))),
        heat_vector_relative_difference=fmt(mp.norm(vec(r,'heat_coefficients')-vec(v,'heat_coefficients'))/mp.norm(vec(v,'heat_coefficients'))),
        residual_squared_absolute_difference=fmt(abs(mp.mpf(r['residual_squared'])-mp.mpf(v['residual_squared']))),
        energy_relative_difference=fmt(abs(mp.mpf(r['Rayleigh_energy'])/mp.mpf(v['Rayleigh_energy'])-1)),
        Wprime0_primary=fmt(derivative(r)),Wprime0_validation=fmt(derivative(v)),
        Wprime0_relative_difference=fmt(abs(derivative(r)/derivative(v)-1)),
        common_T_tail_caveat='Same T320 truncation in both runs; zero-time physical projection controls additionally check this tail',interval_certificate=False)
    (OUT/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
    literal=json.loads((OUT.parent/'main_results.json').read_text())['results'];lit={int(x['m']):x for x in literal if x['family']=='heat'}
    comparisons=[];fits=[]
    for r in a:
        wm=r['window_m'];z=lit[wm];wp=derivative(r)
        comparisons.append(dict(window_m=wm,N=r['N'],literal_N=wm,literal_s_star=z['s'],resolution_s_star=r['s_star'],s_difference=fmt(mp.mpf(r['s_star'])-mp.mpf(z['s'])),literal_heat_residual_squared=z['residual_squared'],resolution_heat_residual_squared=r['residual_squared'],residual_ratio_to_literal=fmt(mp.mpf(r['residual_squared'])/mp.mpf(z['residual_squared'])),Wprime0_resolution=fmt(wp)))
        fits.append(dict(window_m=wm,N=r['N'],L=r['L'],lambda0=r['lambda0'],s_star=r['s_star'],candidate_type='s=0 boundary' if mp.mpf(r['s_star'])==0 else 'interior stationary',w0=r['w0'],w_star=r['w_star'],residual_squared=r['residual_squared'],Wprime_at_candidate=fmt(wp),residual_squared_right_derivative=fmt(-wp),boundary_KKT_pass=bool(wp<=0),Rayleigh_energy=r['Rayleigh_energy'],energy_over_lambda0=r['energy_over_lambda0'],zero_time_projection_relative_error=r['zero_time_projection_relative_error'],all_s_ge_1_overlap_upper=r['all_s_ge_1_overlap_upper']))
    write_csv('fits.csv',fits);write_csv('comparison.csv',comparisons)
    r8=[r for r in a if r['window_m']==8];conv=[]
    for x,y in zip(r8,r8[1:]):
        conv.append(dict(window_m=8,N_left=x['N'],N_right=y['N'],lambda_ratio=fmt(mp.mpf(x['lambda0'])/mp.mpf(y['lambda0'])),residual_squared_relative_change=fmt(mp.mpf(y['residual_squared'])/mp.mpf(x['residual_squared'])-1),s_difference=fmt(mp.mpf(y['s_star'])-mp.mpf(x['s_star']))))
    write_csv('resolution_changes.csv',conv)
    lines=['# Fixed-window heat-fit resolution canary','','**DIAGNOSTIC_NEVER_A_PROOF.**','',
           'The best candidates found for all four higher-resolution cells are the forward-domain boundary s=0. Thus forward heat provides no improvement over the unheated theta profile in this scan. The one-sided overlap derivative is strictly negative at that boundary, so a zero stationary derivative is neither expected nor required.','',
           '|window m|N|s*|W(0)=W*|Residual squared|W\'(0)|E/lambda0|','|---:|---:|---:|---:|---:|---:|---:|']
    for r in fits:lines.append(f"|{r['window_m']}|{r['N']}|0|{float(r['w_star']):.12g}|{float(r['residual_squared']):.12g}|{float(r['Wprime_at_candidate']):.12g}|{float(r['energy_over_lambda0']):.8g}|")
    lines+=['','The literal schedules had positive best-fit temperatures: s8=0.001287763472... and s12=0.002633246404.... Increasing N at fixed L changes the best-found constrained fit to s=0 in these cells. This establishes a finite resolution sensitivity of the positive-temperature interpretation; it does not establish a limiting temperature or a general plateau-artifact theorem.','',
            'For log8, lambda44/lambda56='+mp.nstr(mp.mpf(r8[0]['lambda0'])/mp.mpf(r8[1]['lambda0']),14)+' and lambda56/lambda68='+mp.nstr(mp.mpf(r8[1]['lambda0'])/mp.mpf(r8[2]['lambda0']),14)+'. The bottom eigenvalues are still changing substantially. A repeated boundary value s=0 is not a convergence certificate.','',
            'At s=0 the Rayleigh energy is the baseline projected-theta energy, not an improved fitted energy. It remains many orders above lambda0. Small L2 residuals therefore do not provide the missing spectral/energy bound.','',
            'All lengths are L=log(window_m), independent of N; only modes change. The active prime sum retains every prime power with log(k)<L. No high-resolution N is substituted into the window or prime cutoff.','',
            'Primary calculations: 140 dps, eight-panel matrix GL128, spectral GL56 in width4 panels through T320. One-cell validation (log8,N68): 160 dps, matrix GL160, spectral GL64 through T320. No interval arithmetic is used. Full validation deltas are in validation.json. The common Fourier cutoff is additionally checked by comparing zero-time spectral projection to physical theta projection.','',
            'curve_probes.csv contains high-precision W(s) and derivatives at s=0,0.0001,0.001,0.003,0.01. boundary_conditions.csv records W\'(0)<0 and residual\'(0)>0. grid.csv contains the complete float64 candidate-search grid; it is not a certificate.','',
            'The analytic large-time bound from ../heat_review.md is evaluated for each target and excludes all s>=1 from beating the baseline. The compact search in [0,1] is best-found, not an exhaustive interval proof of global optimality. No negative heat time is evaluated.','',
            'Raw main_results.json preserves the generic field name stationary_residual from the fitter; at s=0 this is the nonzero gradient numerator, not a failed stationarity test. fits.csv gives its correct boundary/KKT interpretation.','',
            'Provenance and all ground/heat/residual coefficients are in main_results.json and validation_results.json. Matrix construction is replayable from matrix_core.py; heat projection uses the parent full-line heat_fit.py.','',
            'Replay:','```bash','uv run --with mpmath --with numpy --with scipy resolution_fit.py','uv run --with mpmath --with numpy --with scipy resolution_fit.py --dps 160 --matrix-order 160 --spectral-order 64 --validation','uv run --with mpmath --with numpy --with scipy boundary_checks.py','uv run --with mpmath finalize.py','```']
    (OUT/'RESULT.md').write_text('\n'.join(lines)+'\n')
    print(json.dumps(validation,indent=2))
    for r in fits:print(r['window_m'],r['N'],mp.nstr(mp.mpf(r['Rayleigh_energy']),16),mp.nstr(mp.mpf(r['energy_over_lambda0']),16))
if __name__=='__main__':main()
