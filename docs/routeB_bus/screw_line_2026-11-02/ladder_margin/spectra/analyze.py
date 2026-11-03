from spectra import *
r=list(csv.DictReader((P/'metrics.csv').open()));eq=list(csv.DictReader((P/'equal_count_metrics.csv').open()));tc=list(csv.DictReader((P/'tail_convergence.csv').open()));table=[];decisions=[];calibration=[]
for mesh in [32,64,128,256]:
 def vals(world,cut=400):return np.array([float(x['primary_median']) for x in r if x['world']==world and int(x['mesh'])==mesh and int(x['cut'])==cut])
 po=vals('poisson');gu=vals('gue_bulk');pi=vals('picket')[0];zs=vals('zeta_surrogate')[0];za=vals('zeta_arithmetic_reference',0)[0];lo,hi=np.quantile(gu,[.025,.975]);pg=float(np.mean(po<gu));gp=float(np.mean(gu<pi))
 table.append(dict(mesh=mesh,poisson_median=float(np.median(po)),gue_median=float(np.median(gu)),gue_q025=float(lo),gue_q975=float(hi),zeta_surrogate=zs,zeta_arithmetic=za,picket=pi,poisson_below_gue_fraction=pg,gue_below_picket_fraction=gp,zeta_surrogate_inside_gue95=bool(lo<=zs<=hi),actual_zeta_inside_gue95=bool(lo<=za<=hi)))
 calibration.append(dict(mesh=mesh,absolute_surrogate_source_difference=abs(zs-za),pass_point02=bool(abs(zs-za)<=.02)))
 decisions.append(dict(mesh=mesh,primary_ordering_pass=bool(pg>=.75 and gp>=.75 and lo<=zs<=hi)))
robust=[]
for mesh in [32,64,128,256]:
 for cut in [400,800,1600]:
  po={int(x['rep']):float(x['primary_median']) for x in r if x['world']=='poisson' and int(x['mesh'])==mesh and int(x['cut'])==cut and int(x['rep'])<4};gu={int(x['rep']):float(x['primary_median']) for x in r if x['world']=='gue_bulk' and int(x['mesh'])==mesh and int(x['cut'])==cut and int(x['rep'])<4};pi=next(float(x['primary_median']) for x in r if x['world']=='picket' and int(x['mesh'])==mesh and int(x['cut'])==cut)
  robust.append(dict(mesh=mesh,control='cutoff',cut=cut,poisson_median=float(np.median(list(po.values()))),gue_median=float(np.median(list(gu.values()))),picket=pi,poisson_below_gue_fraction=sum(po[k]<gu[k] for k in po)/len(po),gue_below_picket_fraction=sum(v<pi for v in gu.values())/len(gu)))
 po={int(x['rep']):float(x['primary_median']) for x in eq if x['world']=='poisson_equal_count' and int(x['mesh'])==mesh};gu={int(x['rep']):float(x['primary_median']) for x in eq if x['world']=='gue_bulk_equal_count' and int(x['mesh'])==mesh};pi=next(float(x['primary_median']) for x in eq if x['world']=='picket_equal_count' and int(x['mesh'])==mesh)
 robust.append(dict(mesh=mesh,control='equal_count202',cut=400,poisson_median=float(np.median(list(po.values()))),gue_median=float(np.median(list(gu.values()))),picket=pi,poisson_below_gue_fraction=sum(po[k]<gu[k] for k in po)/len(po),gue_below_picket_fraction=sum(v<pi for v in gu.values())/len(gu)))
tailchecks=[]
for world in ['zeta_surrogate','picket']:
 for mesh in [32,64,128,256]:
  a=next(x for x in tc if x['world']==world and int(x['mesh'])==mesh and int(x['power'])==22);b=next(x for x in tc if x['world']==world and int(x['mesh'])==mesh and int(x['power'])==24)
  tailchecks.append(dict(world=world,mesh=mesh,metric_change=abs(float(a['primary_median'])-float(b['primary_median'])),block_mu_change=abs(float(a['mu_a6_q32'])-float(b['mu_a6_q32']))))
write('ordering.csv',table);write('robustness.csv',robust);write('tail_validation.csv',tailchecks)
result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',calibration=calibration,actual_zeta_calibration_pass=all(x['pass_point02'] for x in calibration),primary_ordering=decisions,all_mesh_primary_ordering_pass=all(x['primary_ordering_pass'] for x in decisions),tail_resolution_pass=all(x['metric_change']<.001 for x in tailchecks),unresolved_model_cells=sum(x['status']!='POSITIVE' and x['world']!='zeta_arithmetic_reference' for x in r),note='Model comparison only if arithmetic-zeta calibration fails; no actual-zeta law or proof.')
if (P/'bin_convergence.csv').exists():
 bins=list(csv.DictReader((P/'bin_convergence.csv').open()));differences=[]
 for world in ['zeta_surrogate','picket']:
  for mesh in [32,64,128,256]:
   aa=next(v for v in bins if v['world']==world and int(v['mesh'])==mesh and int(v['period'])==16);bb=next(v for v in bins if v['world']==world and int(v['mesh'])==mesh and int(v['period'])==64)
   differences.append((abs(float(aa['primary_median'])-float(bb['primary_median'])),abs(float(aa['mu_a6_q32'])-float(bb['mu_a6_q32']))))
 result['frequency_bin_max_metric_change']=max(x[0] for x in differences);result['frequency_bin_max_block_change']=max(x[1] for x in differences);result['frequency_bin_resolution_pass']=result['frequency_bin_max_metric_change']<.001
(P/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));print(json.dumps(table,indent=2))
