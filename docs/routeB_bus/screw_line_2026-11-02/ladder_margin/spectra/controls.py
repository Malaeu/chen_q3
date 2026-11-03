from spectra import *
import shutil

def reference():
 import sys,mpmath as mp
 core=BUS/'screw_line_2026-11-02/innovation_law/core';sys.path.insert(0,str(core));from scan import source
 rows=[]
 for mesh in [32,64,128,256]:
  mp.mp.dps=90;saved=json.loads((core/f'zeta_mesh{mesh}_dps100.json').read_text());g,_=source('zeta',mp.mpf('6.3'));gs=list(map(mp.mpf,saved['g_values']));last=2*gs[-1]-gs[-2]-g(mp.mpf(6)+mp.mpf(1)/mesh)
  rr=np.r_[np.array(saved['r_values'],float),float(last)];v,status=levinson(rr);mu=v/rr[0];x=np.arange(len(mu))/mesh
  rows.append(dict(world='zeta_arithmetic_reference',rep=0,cut=0,mesh=mesh,status='MP100_SOURCE_PLUS_ONE_MP90_ENDPOINT',resolved_prefixes=len(mu),primary_median=float(np.median(mu[(x>=1)&(x<=6)])),minimum_margin=float(mu[(x>=1)&(x<=6)].min())))
 return rows

def main():
 start=time.monotonic();raw=list(csv.DictReader((P/'metrics.csv').open()));refs=reference()
 raw=[r for r in raw if r['world']!='zeta_arithmetic_reference']+refs;write('metrics.csv',raw)
 specs=json.loads((P/'generated_spectra.json').read_text());known=list(csv.DictReader((BUS/'capacity_matrix_2026-11-02/zeros.csv').open()));z=np.array([float(x['gamma']) for x in known]);z=z[z<400];count=len(z);u0=F(z[0]);uc=F(400)
 tg,_=tail(400);summaries=[];profiles=[];multis=[];density=[]
 for spec in specs:
  h=np.array(spec['heights']);u=F(h)
  for cut in [400,800,1600]:
   use=u[h<cut]
   density.append(dict(world=spec['world'],rep=spec['rep'],cut=cut,count=len(use),expected_smooth_count=float(F(cut)-u0+1),mean_unfolded_spacing=float(np.diff(use).mean()),minimum_spacing=float(np.diff(use).min())))
  if spec['world']!='picket' and spec['rep']>=4:continue
  positions=u0+(u[:count]-u0)*(uc-u0)/(u[count]-u0);hz=invert(positions);values=spectral(hz)+tg
  run_cell(spec['world']+'_equal_count',spec['rep'],400,values,profiles,multis,summaries)
  print('CONTROL',spec['world'],spec['rep'],flush=True)
 write('equal_count_metrics.csv',summaries);write('equal_count_profiles.csv',profiles);write('equal_count_blocks.csv',multis);write('density_checks.csv',density)
 (P/'control_run.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',seconds=time.monotonic()-start,count=count,arithmetic_reference_index_correction=True),indent=2)+'\n')
 if Path('/tmp/ladder_spectra_wrong_density_initial/metrics.csv').exists():shutil.copyfile('/tmp/ladder_spectra_wrong_density_initial/metrics.csv',P/'initial_density_error_metrics.csv')
if __name__=='__main__':main()
