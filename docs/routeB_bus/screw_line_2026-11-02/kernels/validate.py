"""Source and precision replay for the formal inverse-form diagnostic."""
from pathlib import Path
import argparse,json,hashlib
import mpmath as mp
from flint import arb_mat,arb,ctx
from screw_kernels import source_matrix,coefficients,text

def main():
 p=argparse.ArgumentParser();p.add_argument('--edge-input-root',type=Path,required=True);p.add_argument('--lower-cells',type=Path,required=True);p.add_argument('--edge-capacity',type=Path,required=True);p.add_argument('--output',type=Path,default=Path(__file__).resolve().parent);args=p.parse_args();P=args.output;ctx.prec=1024;mp.mp.dps=160;source=[];anchors=[];precision=[]
 preflight=json.loads((P/'preflight_source_anchor_records.json').read_text()) if (P/'preflight_source_anchor_records.json').exists() else []
 def getcase(world,m):
  fp=P/f'{world}_m{m}_bits1024.json'
  if fp.exists():return json.loads(fp.read_text())
  return next((a for a in preflight if a['world']==world and a['m']==m),None)
 for world in ['zeta','dh']:
  b=coefficients(240,world)
  for m in [55,120,240]:
   q=27 if m==55 and world=='zeta' else 50 if m==55 else 64 if m==120 and world=='zeta' else 108 if m==120 else 139 if world=='zeta' else 216
   fn=f'{world}_m{m}_q{q}'+('_native' if world=='dh' and m<240 else '')+'.json'
   path=(args.lower_cells/fn) if m<240 else args.edge_input_root/'dense'/f'{world}_m{m}_q{q}_rebuild.json'
   d=json.loads(path.read_text());A,_=source_matrix(m,world,b);S=arb_mat(d['A']);D=A-S;err=max(abs(v) for v in D.entries());f=d['complement_f'];F=arb_mat([[v[0] if isinstance(v,list) else v] for v in f]);energy=(F.transpose()*D*F)[0,0];lam=arb(d['complement_minimum']);rel=abs(energy)/abs(lam)
   source.append(dict(world=world,m=m,q=q,source_file=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),max_A_entry_difference=text(err),saved_vector_energy_difference=text(energy),relative_saved_compressed_minimum_energy_difference=text(rel),pass_entry_abs_1e_90=bool(err<arb('1e-90')),pass_relative_compressed_energy_1e_60=bool(rel<arb('1e-60'))))
 # Every available native EDGE capacity is an independent QR-coordinate check
 # against the new raw-E congruence evaluation, not merely an A-entry check.
 for world in ['zeta','dh']:
  for m,q in ([(55,27),(80,41),(120,64),(160,89),(200,115),(240,139)] if world=='zeta' else [(55,50),(80,73),(120,108),(160,144),(200,180),(240,216)]):
   name=f'{world}_m{m}_q{q}'+('_native' if world=='dh' and m<=120 else '_rebuild' if m>=160 else '')+'_capacity_dps80.json';cp=args.edge_capacity/name
   if not cp.exists():raise FileNotFoundError(cp)
   capd=json.loads(cp.read_text());cap=mp.mpf(capd['capacity_algebraic'])
   reference='EDGE80dps'
   if world=='dh' and m==240:
    cap=mp.mpf(json.loads((args.edge_capacity/'worst_inverse_validation.json').read_text())['high_cap']);reference='EDGE110dps_worst_inverse'
   if world=='zeta' and m==240:
    h=json.loads((args.edge_capacity/'zeta_m240_q139_rebuild_capacity_dps110.json').read_text());cap=mp.mpf(h['capacity_algebraic']);reference='EDGE110dps'
   kr=getcase(world,m)
   if kr is None:continue
   K=mp.mpf(kr['rows'][0]['K']);err=abs(K-1/cap)/abs(1/cap)
   anchors.append(dict(world=world,m=m,q=q,reference=reference,congruence_K=mp.nstr(K,80),QR_inverse_capacity=mp.nstr(1/cap,80),relative_difference=mp.nstr(err,70),pass_relative_1e_12=bool(err<mp.mpf('1e-12'))))
 for folder in [P/'precision_check',P/'onset_precision']:
  for hp in sorted(folder.glob('*_bits1536.json')):
   hi=json.loads(hp.read_text());lo=getcase(hi['world'],hi['m'])
   if lo is None:continue
   diff=[]
   for a,b in zip(lo['rows'],hi['rows']):
    for key in ['K','endpoint_cross','r_proxy','r_proxy_squared']:
     if a[key]=='':continue
     x=mp.mpf(a[key]);y=mp.mpf(b[key]);err=abs(x-y)/max(abs(y),mp.mpf('1e-5000'));diff.append(dict(gauge=a['gauge'],eta=a['eta'],field=key,relative_difference=mp.nstr(err,70),pass_relative_1e_40=bool(err<mp.mpf('1e-40'))))
   precision.append(dict(world=hi['world'],m=hi['m'],low_bits=1024,high_bits=1536,inertia_matches=lo['inertia']['negative']==hi['inertia']['negative'],comparisons=diff,max_relative_difference=mp.nstr(max(mp.mpf(a['relative_difference']) for a in diff),70),all_relative_pass=all(a['pass_relative_1e_40'] for a in diff)))
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',source_A_comparisons=source,QR_vs_congruence_endpoint_checks=anchors,precision_checks=precision,pass_all_source=all(a['pass_entry_abs_1e_90'] and a['pass_relative_compressed_energy_1e_60'] for a in source),pass_all_QR_anchors=all(a['pass_relative_1e_12'] for a in anchors),pass_all_precision=all(a['inertia_matches'] and a['all_relative_pass'] for a in precision))
 (P/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k.startswith('pass_')},indent=2));print('anchors',len(anchors),'precision',len(precision))
 if not all(result[k] for k in ['pass_all_source','pass_all_QR_anchors','pass_all_precision']):raise SystemExit(1)
if __name__=='__main__':main()
