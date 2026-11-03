from spectra import *
known=list(csv.DictReader((BUS/'capacity_matrix_2026-11-02/zeros.csv').open()));z=np.array([float(x['gamma']) for x in known]);z=z[z<400];u0=F(z[0]);pick=invert(np.arange(1400)+u0);rows=[]
for power,period in [(22,16),(23,32),(24,64)]:
 tg,_=tail(400,power,period)
 for world,heights in [('zeta_surrogate',z),('picket',pick[pick<400])]:
  g=getter(spectral(heights)+tg)
  for mesh in [32,64,128,256]:
   h=1/mesh;gs=g(np.arange(6*mesh+2)*h);rr=np.r_[-2*gs[1],2*gs[1:-1]-gs[:-2]-gs[2:]];vv,status=levinson(rr);mu=vv/rr[0];x=np.arange(len(mu))/mesh
   rows.append(dict(world=world,period=period,power=power,mesh=mesh,status=status,primary_median=float(np.median(mu[(x>=1)&(x<=6)])),mu_a6_q32=block(g,rr,6*mesh,h,32)))
write('bin_convergence.csv',rows)
print('bin convergence complete')
