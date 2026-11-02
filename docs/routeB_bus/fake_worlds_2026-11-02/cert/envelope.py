"""DIAGNOSTIC_NEVER_A_PROOF: evaluate DH (7.1) with saved native quiet data.
Run: uv --offline run --with mpmath python3 envelope.py
No interval certification of R, delta, the zero census, or Q is performed here.
"""
from pathlib import Path
import csv,json,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent
SOURCE=P.parent/'ledger_diff/matched_cells'
mp.mp.dps=120
CD=mp.euler+mp.log(8*mp.pi/5)-mp.pi/2
ROWS=[]
for m,q in ((55,50),(80,73),(120,108)):
    path=SOURCE/f'dh_m{m}_q{q}_native.json'
    d=json.loads(path.read_text())
    R=-min(mp.mpf(x) for x in d['full_eigenvalues'])
    delta=mp.mpf(d['delta'])
    if not (R>delta>=0):
        raise ArithmeticError(f'm={m}: numerical delta<R hypothesis fails')
    correction=delta**2/(R-delta)
    upper=-R+correction
    cviol=R-correction-CD
    observed=mp.mpf(d['complement_minimum'])
    fmt=lambda x:mp.nstr(x,115)
    ROWS.append(dict(status='DIAGNOSTIC_NOT_INTERVAL_CERTIFIED',m=m,q=q,
        cutoff_mode=d['cutoff_mode'],kappa=d['effective_kappa'],
        evaluation_dps=120,input_evaluation_dps=d['dps'],
        R=fmt(R),delta=fmt(delta),delta_lt_R=True,c_D_positive=fmt(CD),
        correction_delta_squared_over_R_minus_delta=fmt(correction),
        complement_upper_envelope=fmt(upper),
        C_violation_threshold=fmt(cviol),
        C_zero_upper_including_c_D=fmt(upper+CD),
        observed_complement_minimum=fmt(observed),
        observed_minimum_below_envelope=bool(observed<=upper),
        source_file=str(path.relative_to(P.parent)),
        source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        matrix_source_pin='d26831357b6cb3b2b7d4a569d2031e454952b246',
        delta_and_zero_coordinates_interval_certified=False))
with (P/'envelope.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=ROWS[0]);w.writeheader();w.writerows(ROWS)
lines=[
    '# DH complement envelope — diagnostic only','',
    '**DIAGNOSTIC_NOT_INTERVAL_CERTIFIED.** These are 120-digit evaluations of saved native κ=1.1 data. Neither the true-Q residual δ nor the zero census/coordinates is interval-certified by this computation. The source matrix is the pole-free DH form pinned at d26831357b6cb3b2b7d4a569d2031e454952b246.','',
    'Equation (7.1) assumes λ_min(A)=−R<0, Q isometric, and ||AQ||≤δ<R. Its complement upper envelope is −R+δ²/(R−δ). Here R comes from the saved full spectrum, not from the complement eigenvalue. The positive constant is c_D=γ+log(8π/5)−π/2='+mp.nstr(CD,24)+', the negative of the original signed constant.','',
    '|m|R|δ|upper envelope|C_violation|',
    '|---:|---:|---:|---:|---:|']
for r in ROWS:
    lines.append('|'+str(r['m'])+'|'+'|'.join(mp.nstr(mp.mpf(r[k]),18) for k in ('R','delta','complement_upper_envelope','C_violation_threshold'))+'|')
lines += ['',
    'C_violation=R−δ²/(R−δ)−c_D. If the inputs and hypotheses were independently certified, every fixed C<C_violation would make the envelope plus C+c_D strictly negative. The displayed positive thresholds are diagnostic numerical findings, not certified complement-floor violations.','',
    'An independently certified negative Rayleigh upper establishes the existence of a negative direction. It does not by itself certify the numerical full minimum R, the true interpolation residual δ, or this projected envelope. No global/cofinal conclusion is drawn here.','',
    'The CSV retains input SHA-256 hashes, the numerical δ<R check, and the comparison with the saved complement minimum. Replay with `uv --offline run --with mpmath python3 envelope.py`.']
(P/'ENVELOPE.md').write_text('\n'.join(lines)+'\n')
print('Saved envelope.csv and ENVELOPE.md')
