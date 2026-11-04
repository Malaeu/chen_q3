"""Paired pinned-source-order and finite Frobenius conservation checks."""
from source_moments import *
def main():
 data=json.loads((OUT/'SOURCE_MOMENTS.json').read_text());rows=data['rows'];pairs=[]
 for m in [16,40,300]:
  a=np.load(LOCAL/f'm{m}_q192.npz');b=np.load(LOCAL/f'm{m}_q256.npz')
  ra=json.loads((LOCAL/f'm{m}_q192.json').read_text());rb=json.loads((LOCAL/f'm{m}_q256.json').read_text())
  for w in ['zeta','dh','plant']:
   x=next(t for t in ra['rows']if t['world']==w);y=next(t for t in rb['rows']if t['world']==w)
   pairs.append(dict(world=w,m=m,source_bits=400,GL_orders='192,256',A_maxentry_difference=float(np.max(np.abs(a[f'{w}_A']-b[f'{w}_A']))),C_maxentry_difference=float(np.max(np.abs(a[f'{w}_C']-b[f'{w}_C']))),B_maxentry_difference=float(np.max(np.abs(a[f'{w}_B']-b[f'{w}_B']))),Frob2_difference=y['Frob2']-x['Frob2'],Frob2_relative_difference=(y['Frob2']-x['Frob2'])/x['Frob2'],trace_difference=y['trace']-x['trace'],q192_conservation_error=x['conservation_error'],q256_conservation_error=y['conservation_error']))
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',completed_rows=len(rows),expected_rows=855,all_world_m_unique=len({(r['world'],r['m'])for r in rows})==len(rows),max_relative_conservation_error=max(abs(r['conservation_error'])/r['Frob2']for r in rows),max_source_split_maxentry=max(r['C_B_reconstruction_maxerr']for r in rows),max_atom_B_maxentry=max(r['arithmetic_atom_reconstruction_maxerr']for r in rows),paired_order_pilots=pairs)
 (OUT/'SOURCE_MOMENTS_validation.json').write_text(json.dumps(result,indent=2)+'\n');csvwrite('SOURCE_MOMENTS_paired_orders.csv',pairs)
 (OUT/'SOURCE_MOMENTS_validation.md').write_text('# Finite source validation\n\nDIAGNOSTIC_NEVER_A_PROOF. Completed '+str(len(rows))+'/855 world/m rows. Maximum relative Frobenius conservation residual '+str(result['max_relative_conservation_error'])+'. Maximum atom-to-source B entry residual '+str(result['max_atom_B_maxentry'])+'. GL192/256 pilot differences are recorded separately and do not provide a uniform interval quadrature bound. Both paired source builds use unchanged400-bit MPFR and eight panels; displayed moments use binary64.\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
