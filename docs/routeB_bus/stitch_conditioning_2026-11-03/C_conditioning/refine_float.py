"""Replay float-resolved singular triplets with both MP residual equations."""
from scan import *
mp.mp.dps=80;out=[]
for path in sorted(CELLS.glob('*_m*.json')):
 cell=json.loads(path.read_text());changed=False
 for r in cell['rows']:
  if r.get('sigma_status')!='FLOAT_SVD_MP_RAYLEIGH' or r.get('float_replay_version')==2:continue
  E,labels,_,_=rows_for(cell['world'],cell['m'],mp.mpf(r['T']));s=conditioning(cell['world'],cell['m'],mp.mpf(r['T']),E);old=mp.mpf(r['sigma_min']);sm=s['sigma'];byheight={}
  for label,value in zip(labels,s['left']):byheight.setdefault(label['gamma'],mp.mpf(0));byheight[label['gamma']]+=abs(value)**2
  hs=sorted(byheight,key=lambda x:mp.mpf(x));p=max(range(len(hs)-1),key=lambda i:byheight[hs[i]]+byheight[hs[i+1]])
  ratio=2*s['squared']/mp.mpf(r['lambda_r_preferred']) if r['lambda_r_preferred'] is not None and mp.mpf(r['lambda_r_preferred']) else None
  r.update(serial(dict(sigma_min=sm,sigma_min_squared=s['squared'],sigma_dps=s['dps'],sigma_iterations=s['iterations'],sigma_relative_residual=s['relative_residual'],sigma_relative_change=s['relative_change'],sigma_seconds=s['seconds'],sigma_status=s['method'],sigma_float_radius=s.get('float_sigma_radius'),weak_pair_left=hs[p],weak_pair_right=hs[p+1],weak_pair_mass=byheight[hs[p]]+byheight[hs[p+1]],twice_sigma_squared_over_lambda_r=ratio,float_replay_version=2)))
  out.append(dict(world=cell['world'],m=cell['m'],cut=r['cut'],relative_sigma_change=mp.nstr(abs(sm/old-1),25),new_relative_triplet_residual=mp.nstr(s['relative_residual'],25),method=s['method']));changed=True
 if changed:
  temp=path.with_suffix('.replay.tmp');temp.write_text(json.dumps(cell,indent=2)+'\n');temp.replace(path)
prior=json.loads((P/'float_replay.json').read_text()) if(P/'float_replay.json').exists() else [];(P/'float_replay.json').write_text(json.dumps(prior+out,indent=2)+'\n');print('refined',len(out),'maximum sigma relative change',max((float(r['relative_sigma_change']) for r in out),default=0),'maximum triplet residual',max((float(r['new_relative_triplet_residual']) for r in out),default=0))
