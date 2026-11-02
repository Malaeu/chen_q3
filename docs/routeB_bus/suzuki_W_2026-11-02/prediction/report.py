from scan import *
def report():
 rows=[]
 for world in ('zeta','dh','plant'):
  for h in ('.1','.05','.025'):
   d=json.loads((OUT/f'{world}_h{h}_dps80.json').read_text());c=list(csv.DictReader((OUT/f'{world}_h{h}_dps80.csv').open()));last=c[-1]
   rows.append({'world':world,'h':h,'first_negative_t':d['first_negative_t'] or '>6 (censored)','final_negative_inertia':last['negative_inertia'],'final_min_eigenvalue':last['float_eigen_min'],'final_schur':last['schur'],'minimum_schur':str(min(mp.mpf(x['schur']) for x in c)),'float_uncertain_prefixes':sum(int(x['float_unresolved'])>0 for x in c),'max_constant_mode_error':max(float(x['g_return_error']) for x in d['constant_mode_controls'])})
 with (OUT/'summary.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
 text='''# Finite source prediction probe

DIAGNOSTIC_NEVER_A_PROOF.

The source is `ab8d123`, Git blob `b56a16a0540ed3f81858c113bc48de68c909b8c8`; its copy is SOURCE.md. The planted model is **§6.2, (18)**, not §5. It adds gamma=2pi/log2, eta=1/4, multiplicity1 to the actual arithmetic zeta source. The paper's RH-baseline interpretation is conditional; this computation does not assume or establish RH.

|World|h|First negative prefix time|n− at6|Smallest eigenvalue at6|Schur defect at6|
|---|---:|---:|---:|---:|---:|
'''
 for r in rows:text+=f"|{r['world']}|{r['h']}|{r['first_negative_t']}|{r['final_negative_inertia']}|{float(r['final_min_eigenvalue']):.10g}|{float(r['final_schur']):.10g}|\n"
 text+='''
The coarser DH grids miss the negative directions detected at h=.025. The plant detection time also changes with resolution. These are finite sampling results, not intrinsic first failure times of the continuous kernel. The final Schur defect can be positive after the accumulated kernel has become indefinite: inertia is retained independently.

## Source and normalization

Write a=1/2 for zeta, 3/2 for DH and j_a(s)=exp(-a s)/(1-exp(-2s)). With c the signed original constant,

`g(t) = -c |t|/2 - S_a(|t|) + sum_(log n<|t|) b_n/sqrt(n) (|t|-log n) - zeta_pole`,

where `S_a(t)=sum_(r>=0)(1-exp(-(a+2r)t))/(a+2r)^2` and the zeta pole is `16 sinh(t/4)^2`. DH has no pole. Zeta b_n is Lambda(n), including every proper prime power. DH uses every coefficient of the exact logarithmic derivative recurrence from dh_matrix.py, including composite coefficients. The smooth sum is evaluated by trigamma minus a rapidly convergent geometric series, with equivalent dilogarithms near0. Earlier passes used these equivalent expressions separately. At0, g is defined exactly0.

The independent constant-mode quadrature checks m=2,4,8 verify `g(L)=-L A00/2`, retaining both source constants and the pole. See each cell JSON for the error.

## Prediction and range guard

The exact structural t=0 row/column is removed, with its b component exactly0. For every other prefix, signed 80-digit LDL retains **all** pivots, including negatives. With nonzero pivots, Kdagger=K^-1, and the reported defect is `d-b* K^-1 b`. No PSD premise, positive-part inversion, or eigenvalue truncation is used. The guarded pivot threshold is recorded in every row; no run triggered it. Original full K has one additional structural zero. The source matrices and LDL reconstruction residuals are computed in mpmath; all full prefix eigenspectra are also saved in the JSON, with a float64 sign-resolution floor recorded in CSV. No eigenvalue lay inside that diagnostic floor. This is not interval certification.

The 120-digit DH h=.025 replay and separate validation.py compare all prefix Schur values/inertias and source entries; selected full eigendecompositions are checked against120-digit matrices. See validation.json for actual errors. Floating eigenspectrum digits beyond their residual bounds are not claimed.

## Hinges

The hinge CSVs vary only the new point; the preceding h=.1 grid history is fixed on both sides. They test every prime-power threshold up to6, using eps=1e-6 and5e-7 except n=331, where eps=1e-7 and5e-8 avoids the shifted log271+0.2 hinge only4.45502638e-7 away. DH g always retains its additional non-prime-power coefficients; the hinge CSV is a prime-power profile, not a census of all DH hinges. The predicted jump is `-2c+2c sum(alpha)`, alpha=K^-1 b. Additional hinges occur at old sample times plus log n, with jump `-2c alpha_j`; they are not mistaken for unshifted prime thresholds. The sign of a scalar prime coefficient alone does not determine a Schur jump.

## Replay

`uv run --with mpmath --with numpy --with scipy python scan.py WORLD H 80 --no-hinges`, WORLD=zeta/dh/plant, H=.1/.05/.025. Repeat DH,.025 at120digits; run validate.py, hinges.py WORLD, report.py, and plot.py (matplotlib).

profiles.png and profiles.pdf show the fine-grid signed innovations and zeta mesh dependence. A finite positive zeta scan supplies no cofinal positivity bound or canonical Hamiltonian.
'''
 hv={}
 for world in ('zeta','dh','plant'):
  rr=list(csv.DictReader((OUT/f'{world}_hinges.csv').open()));aa=[]
  for i in range(0,len(rr),2):
   x,y=rr[i:i+2];pred=float(y['predicted_jump']);ext=2*float(y['measured_jump'])-float(x['measured_jump'])
   aa.append({'n':int(x['n']),'predicted_jump':pred,'Richardson_jump':ext,'Richardson_absolute_error':abs(ext-pred),'half_step_absolute_error':float(y['absolute_jump_error'])})
  hv[world]={'nonzero_prime_power_hinges':len(aa),'positive_predicted_jumps':sum(x['predicted_jump']>0 for x in aa),'negative_predicted_jumps':sum(x['predicted_jump']<0 for x in aa),'max_half_step_error':max(x['half_step_absolute_error'] for x in aa),'max_Richardson_error':max(x['Richardson_absolute_error'] for x in aa),'rows':aa}
 (OUT/'hinge_validation.json').write_text(json.dumps(hv,indent=2)+'\n')
 text+='\n## Measured controls\n\n'
 for world,v in hv.items():text+=f"- {world}: {v['nonzero_prime_power_hinges']} nonzero prime-power hinges; {v['positive_predicted_jumps']} positive and {v['negative_predicted_jumps']} negative jumps. Maximum smaller-step FD error {v['max_half_step_error']:.3g}; two-step Richardson error {v['max_Richardson_error']:.3g}. These errors are numerical comparisons, not interval bounds.\n"
 text+='\nDH h=.025: all240 prefix inertias match at80/120digits; maximum relative Schur change9.95e-76. At t=5.425 the smallest eigenvalue is +0.0002558001270, at5.45 it is -0.0001224797949. The120-digit full diagonalization residual/orthogonality checks give diagnostic eigenvalue error bounds below1.7e-12 at prefixes217,218,240. Source matrix change bound is1.54e-77.\n'
 (OUT/'RESULT.md').write_text(text)
if __name__=='__main__':report()
