from spectra import *
r=list(csv.DictReader((BUS/'capacity_matrix_2026-11-02/zeros.csv').open()));z=np.array([float(x['gamma']) for x in r]);z=z[z<400];g=getter(spectral(z));rows=[]
for mesh in [32,64,128,256]:
 h=1/mesh;gs=g(np.arange(6*mesh+2)*h);rr=np.r_[-2*gs[1],2*gs[1:-1]-gs[:-2]-gs[2:]];vv,status=levinson(rr)
 rows.append(dict(mesh=mesh,positive_zero_count=len(z),exact_rank_upper_bound=2*len(z),requested_prefixes=6*mesh+1,resolved_prefixes=len(vv),status=status,last_resolved_time=len(vv)/mesh,last_margin=vv[-1]/rr[0]))
write('zero_tail_control.csv',rows)
