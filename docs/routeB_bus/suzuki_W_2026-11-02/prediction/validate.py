from scan import *
def validate():
 mp.mp.dps=120
 a=json.loads((OUT/'dh_h.025_dps80.json').read_text());b=json.loads((OUT/'dh_h.025_dps120.json').read_text());x=list(map(mp.mpf,a['g_values']));y=list(map(mp.mpf,b['g_values']));n=len(x)-1
 ca=list(csv.DictReader((OUT/'dh_h.025_dps80.csv').open()));cb=list(csv.DictReader((OUT/'dh_h.025_dps120.csv').open()))
 diff=max(abs(u-v) for u,v in zip(x,y));out={'status':'DIAGNOSTIC_NEVER_A_PROOF','world':'dh','h':'.025','dps_low':80,'dps_high':120,'max_g_difference':mp.nstr(diff,40),'matrix_operator_difference_bound_from_entrywise':mp.nstr(3*n*diff,40),'all_prefix_inertias_equal':all(u['negative_inertia']==v['negative_inertia'] for u,v in zip(ca,cb)),'max_schur_absolute_difference':mp.nstr(max(abs(mp.mpf(u['schur'])-mp.mpf(v['schur'])) for u,v in zip(ca,cb)),40),'max_schur_relative_difference':mp.nstr(max(abs(mp.mpf(u['schur'])-mp.mpf(v['schur']))/abs(mp.mpf(v['schur'])) for u,v in zip(ca,cb)),40),'spectral_checks':[]}
 for size in (217,218,240):
  K=mp.matrix(size)
  for i in range(size):
   for j in range(size):K[i,j]=y[abs(i-j)]-y[i+1]-y[j+1]
  vals,vec=np.linalg.eigh(np.array(K.tolist(),dtype=float));Q=mp.matrix(vec.tolist());R=K*Q-Q*mp.diag([mp.mpf(float(v)) for v in vals]);orth=mp.norm(Q.T*Q-mp.eye(size));res=mp.norm(R)
  # Polar orthonormalization error: ||Q-O|| <= orth/(1+sqrt(1-orth)).
  correction=orth/(1+mp.sqrt(1-orth));bound=res+correction*(mp.norm(K)+max(abs(float(v)) for v in vals))
  out['spectral_checks'].append({'prefix':size,'t':str(mp.mpf('.025')*size),'float_min':float(vals[0]),'float_max':float(vals[-1]),'orthogonality_Frobenius':mp.nstr(orth,30),'eigen_residual_Frobenius':mp.nstr(res,30),'all_eigenvalue_absolute_error_diagnostic_bound':mp.nstr(bound,30),'minimum_absolute_float_eigenvalue':min(abs(float(v)) for v in vals),'all_signs_resolved':min(abs(float(v)) for v in vals)>bound})
  print('VALIDATED',size,flush=True)
 (OUT/'validation.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':validate()
