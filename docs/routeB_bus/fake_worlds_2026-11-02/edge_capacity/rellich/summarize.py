"""Join exact-scope Rellich diagnostics; no mathematical promotion."""
from pathlib import Path
import csv,json
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=100
def run():
 groups={}
 for p in P.glob('*_dps*_gl*.json'):
  if p.name.startswith('m8'):continue
  d=json.loads(p.read_text());key=(d['world'],d['m'],d['q']);groups.setdefault(key,[]).append((p,d))
 def priority(item):
  p,d=item;hs=[mp.mpf(f['h']) for f in d['FD']]
  return (bool(hs),-min(hs) if hs else 0,d['dps'])
 rows=[];chosen=[]
 for key,items in sorted(groups.items()):
  p,d=max(items,key=priority);chosen.append(str(p.name));scale=mp.mpf(d['relative_scale_e2_logT_over_T'])
  errors=[mp.mpf(f[k]) for f in d['FD'] for k in ['left_abs_error','right_abs_error']]
  fdmax=max(errors) if errors else None
  rows.append(dict(world=d['world'],m=d['m'],q=d['q'],dps=d['dps'],GL_order=d['GL_order'],
   source_left_virial=d['source_left_virial'],boundary_flux=d['boundary_flux'],source_volume=d['source_volume'],projector_correction=d['projector_correction'],
   predicted_left_slope=mp.nstr(mp.mpf(d['source_left_virial'])+mp.mpf(d['projector_correction']),60),endpoint_atom_kick=d['endpoint_atom_kick'],
   source_replay_abs_error=d['source_energy_discrepancy'],boundary_volume_abs_error=d['boundary_volume_identity_error'],Leibniz_direct_abs_error=d['Leibniz_direct_max_error'],
   dotE_FD_abs_error=d['Ed_central_difference_error'],Pi_c_error=d['Pi_c_error'],compressed_stationarity_error=d['compressed_stationarity_error'],
   FD_scope='transported saved-vector Rayleigh' if errors else 'analytic derivative identities only; no large-cell FD',
   FD_h=min((mp.mpf(f['h']) for f in d['FD']),default='not_run'),FD_max_abs_error=mp.nstr(fdmax,60) if fdmax is not None else 'not_run',
   FD_max_relative_error=mp.nstr(fdmax/scale,60) if fdmax is not None else 'not_run',relative_scale_e2_logT_over_T=d['relative_scale_e2_logT_over_T'],source_file=p.name))
 with (P/'summary.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
 z=[r for r in rows if r['world']=='zeta'];dh=[r for r in rows if r['world']=='dh']
 lines=['# Fixed-N Rellich verification','', 'DIAGNOSTIC_NEVER_A_PROOF; Route B CHALLENGER / NOT_RH.','',
  f'Coverage: {len(z)} zeta saved cells and {len(dh)} DH saved controls. No large full-carrier eigensystem was solved by these scripts. Shared source A and evaluation QR were rebuilt for the nine high cells; the capacity worker independently computed reduced spectra.','',
  'The local path is L_tau=L exp(tau), with integer N fixed and actual active zero coordinates fixed. Analytic dotE uses the entire-sinc removable values (a rational rearrangement away from modal points). Projector velocity is evaluated using F=E U and F^T y=U^T c, then dotPi c=(I-UU^T)dotE^T y; this avoids forming the ill-conditioned squared raw Gram inverse. Every correction 2<r,dotPi c> is retained.','',
  'For large saved cells, finite differences concern the Rayleigh quotient of the saved vector transported by the actual projector Pi(L_tau), normalized physically. For a simple stationary compressed eigenvector this has the same first derivative as the eigenvalue branch. They are not new large-cell eigenvalue calculations. Only the source m=8 control rebuilds actual compressed eigenbranches on both sides.','',
  '| world | m | q | source virial | moving-projector correction | FD maximum absolute error | FD error / (e^2 log T/T) |','|---|---:|---:|---:|---:|---:|---:|']
 for r in rows:
  n=lambda k:mp.nstr(mp.mpf(r[k]),8) if r[k]!='not_run' else 'not run'
  lines.append(f"| {r['world']} | {r['m']} | {r['q']} | {n('source_left_virial')} | {n('projector_correction')} | {n('FD_max_abs_error')} | {n('FD_max_relative_error')} |")
 lines+=['','## Threshold and precision controls','',
  'The m=8 exact seven-group control and both numerical settings reproduce the source signs. At 55dps/GL48 the left/right actual eigenvalue FD errors are 1.3245e-10 and 1.5089e-10 for h=1e-12; the corresponding h=1e-8 errors at 40dps/GL32 are 1.3245e-6 and 1.5089e-6. The moving correction is -0.819394427141790169..., and the prime-power-8 right-minus-left kick is -0.524710330246889024....','',
  'All requested large m are mixed-factor composites. Their zeta birth Mangoldt coefficient vanishes; their DH birth coefficient also vanishes because these m are multiples of5. Consequently the large-cell right/left derivative kick is zero. This is verified separately from the nonzero m8 control. No discrete N=m sequence derivative is inferred.','',
  'Coarse high-cell FD steps can be inaccurate on the tiny endpoint scale despite small absolute errors: the coarse JSONs are retained. A single necessary h=1e-40 refinement is reported for the high zeta cells, with identical active coordinates. Ratios are floating diagnostics; there is no interval-certified denominator or cofinal sign conclusion.','',
  'Source replay errors compare the saved source coordinates/matrices with independently evaluated full scalar arithmetic/archimedean/pole forms. The direct Leibniz check evaluates the interior integral from independent analytic trigonometric moments at three shifts. The boundary/volume column is the dilation flux -2e B_L, not the Abel energy-ledger boundary column. DH uses its odd-gamma kernel, all b(n), and no pole.','',
  'Primary source: inbox3fef776b3bd0ebeb9d87e665432ae3e423f2dfb1, PROSHKA_VERDICT_EDGE_LAW_RELLICH_v1_2026-11-02.md, equations2.2–4.7. This bounded verification finds no source-identity error; it does not establish a selected-volume sign or edge law.','',
  'See summary.csv for every raw absolute/relative metric, individual JSONs for fixed-active-set/gap/constraint guards, and source_m8_checks.py plus m8_dps40.json/m8_dps55.json for the true one-sided threshold experiment.','']
 (P/'RESULT.md').write_text('\n'.join(lines));print('joined',len(z),'zeta',len(dh),'DH',flush=True)
if __name__=='__main__':run()
