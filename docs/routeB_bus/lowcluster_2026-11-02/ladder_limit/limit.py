"""NOESCAPE Q4 limiting-ladder canary. DIAGNOSTIC_NEVER_A_PROOF.
All inner products are in L2(R) after zero extension, never coefficient-space
inner products across distinct windows. Data pinned to rh_clean@211bba33b958.
"""
from pathlib import Path
import json,csv,hashlib
import mpmath as mp
mp.mp.dps=100
OUT=Path(__file__).resolve().parent;SOURCE=OUT.parent
MS=(12,16,20,24)
def fmt(v):return mp.nstr(v,80)
def csvout(name,rows):
 with (OUT/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def read(m,high=False):
 fn=f'core_m{m}_dps140_gl160.json' if high else f'core_m{m}_dps100_gl128.json'
 r=json.loads((SOURCE/fn).read_text())
 return dict(m=m,L=mp.log(m),b=mp.log(m)/2,V=mp.matrix(r['V'])[:,:8],source=r)

def basis_cross(a,b,radius=None):
 """Integral of the two zero-extended even bases on their common support."""
 c=min(a['b'],b['b']) if radius is None else min(radius,a['b'],b['b'])
 A=mp.matrix(a['m']+1,b['m']+1)
 for n in range(a['m']+1):
  u=2*mp.pi*n/a['L'];dn=mp.sqrt(2) if n else 1
  for j in range(b['m']+1):
   v=2*mp.pi*j/b['L'];dj=mp.sqrt(2) if j else 1
   A[n,j]=dn*dj*(-1)**(n+j)*c/mp.sqrt(a['L']*b['L'])*(mp.sinc((u-v)*c)+mp.sinc((u+v)*c))
 return A

def basis(x,a):
 if abs(x)>a['b']:return mp.zeros(a['m']+1,1)
 return mp.matrix([(mp.sqrt(2) if n else 1)*(-1)**n*mp.cos(2*mp.pi*n*x/a['L'])/mp.sqrt(a['L']) for n in range(a['m']+1)])

def main():
 data={m:read(m) for m in MS};gram={};rows=[];orth=[]
 for m in MS:
  for n in MS:
   if m>n:gram[m,n]=gram[n,m].T;continue
   a,b=data[m],data[n];C=a['V'].T*basis_cross(a,b)*b['V'];gram[m,n]=C
   if m==n:orth.append(max(abs(v) for v in C-mp.eye(8)))
   for i in range(8):
    for j in range(8):rows.append(dict(m=m,m_prime=n,i=i,j=j,signed_inner=fmt(C[i,j]),absolute_inner=fmt(abs(C[i,j])),consecutive=(n in MS and MS.index(n)==MS.index(m)+1)))
 csvout('physical_gram_all_pairs.csv',rows)
 csvout('physical_gram_consecutive.csv',[r for r in rows if r['consecutive']])
 pairs=[];angles=[];individual=[]
 for m,n in zip(MS,MS[1:]):
  C=gram[m,n]
  for i in range(8):
   best=max(range(8),key=lambda j:abs(C[i,j]))
   individual.append(dict(m=m,m_prime=n,i=i,same_level_overlap=fmt(abs(C[i,i])),same_level_distance_sign_aligned=fmt(mp.sqrt(max(mp.mpf(0),2-2*abs(C[i,i])))),best_matching_level=best,best_overlap=fmt(abs(C[i,best]))))
  summary=dict(m=m,m_prime=n,diagonal_overlaps=[fmt(abs(C[i,i])) for i in range(8)],subspaces=[])
  for r in range(1,9):
   _,s,_=mp.svd_r(C[:r,:r],full_matrices=False)
   ang=[mp.acos(min(mp.mpf(1),max(mp.mpf(0),x))) for x in s]
   ss=dict(dimension=r,cosines=[fmt(x) for x in s],angles_degrees=[fmt(x*180/mp.pi) for x in ang],max_angle_degrees=fmt(max(ang)*180/mp.pi),projector_gap=fmt(mp.sin(max(ang))),chordal_distance=fmt(mp.sqrt(mp.fsum(1-x*x for x in s))))
   summary['subspaces'].append(ss)
   for i in range(r):angles.append(dict(m=m,m_prime=n,dimension=r,angle_index=i,cosine=fmt(s[i]),angle_degrees=fmt(ang[i]*180/mp.pi)))
  pairs.append(summary)
 csvout('individual_overlaps.csv',individual);csvout('consecutive_principal_angles.csv',angles)
 # Pooled map with 32 unit physical columns (eight per cell), equal weights.
 G=mp.matrix(32)
 for a,m in enumerate(MS):
  for b,n in enumerate(MS):
   for i in range(8):
    for j in range(8):G[8*a+i,8*b+j]=gram[m,n][i,j]
 ee,U=mp.eigsy(G);inds=list(reversed(range(32)));raw=[ee[i] for i in inds]
 assert min(raw)>-mp.mpf('1e-85'),min(raw)
 vals=[max(mp.mpf(0),x) for x in raw];sing=[mp.sqrt(x) for x in vals];W=mp.matrix([[U[i,j] for j in inds] for i in range(32)])
 tol=mp.mpf('.01');relrank=sum(s>tol*sing[0] for s in sing);absrank=sum(s>tol for s in sing)
 spectrum=[];reconstruct=[];uniformrank=None;frobrank=None
 for r in range(33):
  errs=[mp.sqrt(max(mp.mpf(0),G[j,j]-mp.fsum(vals[k]*W[j,k]**2 for k in range(r)))) for j in range(32)]
  errmax=max(errs);rms=mp.sqrt(mp.fsum(e*e for e in errs)/32)
  if uniformrank is None and errmax<=tol:uniformrank=r
  if frobrank is None and rms<=tol:frobrank=r
  reconstruct.append(dict(rank=r,max_column_L2_error=fmt(errmax),RMS_column_L2_error=fmt(rms),relative_operator_error=fmt(sing[r]/sing[0]) if r<32 else '0',worst_column_index=max(range(32),key=lambda j:errs[j])))
 for k in range(32):spectrum.append(dict(index=k+1,singular_value=fmt(sing[k]),relative_singular_value=fmt(sing[k]/sing[0]),gram_eigenvalue=fmt(raw[k]),retained_relative_1e_minus_2=(k<relrank),retained_absolute_1e_minus_2=(k<absrank)))
 csvout('pooled_singular_values.csv',spectrum);csvout('pooled_reconstruction.csv',reconstruct)
 # Explicit normalized common POD functions as linear combinations of columns.
 weights=[]
 for k in range(max(relrank,uniformrank)):
  for j in range(32):weights.append(dict(POD_index=k,m=MS[j//8],level=j%8,physical_combination_coefficient=fmt(W[j,k]/sing[k])))
 csvout('common_subspace_coefficients.csv',weights)
 # Physical sampled representation for inspection (not used in inner products).
 samples=[];coefs=[]
 for m in MS:
  a=data[m]
  for n in range(m+1):
   for i in range(8):coefs.append(dict(m=m,level=i,mode=n,coefficient=fmt(a['V'][n,i]),omega=fmt(2*mp.pi*n/a['L'])))
 for j in range(401):
  x=data[24]['b']*(mp.mpf(j)/200-1);r={'x':mp.nstr(x,25)}
  for m in MS:
   v=data[m]['V'].T*basis(x,data[m])
   for i in range(8):r[f'm{m}_v{i}']=mp.nstr(v[i],25)
  samples.append(r)
 csvout('physical_cluster_samples.csv',samples);csvout('physical_cluster_coefficients.csv',coefs)
 # Independent quadrature check of cross Gram 20->24.
 gn,gw=mp.gauss_quadrature(64,'legendre');check=mp.zeros(8);c=data[20]['b']
 for panel in range(8):
  lo=-c+2*c*panel/8;hi=-c+2*c*(panel+1)/8
  for z,w in zip(gn,gw):
   x=(lo+hi+(hi-lo)*z)/2;v=data[20]['V'].T*basis(x,data[20]);vv=data[24]['V'].T*basis(x,data[24]);check+=(w*(hi-lo)/2)*(v*vv.T)
 quadrature_error=max(abs(v) for v in check-gram[20,24])
 high=read(24,True);highC=data[20]['V'].T*basis_cross(data[20],high)*high['V'];high_error=max(abs(v) for v in highC-gram[20,24])
 sources=[]
 for m in MS:
  p=SOURCE/f'core_m{m}_dps100_gl128.json';bb=p.read_bytes();sources.append(dict(file=p.name,sha256=hashlib.sha256(bb).hexdigest()))
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',source_commit='211bba33b9584a6fb81df1bab421d364018e54d7',dps=100,physical_basis='d_n*(-1)^n*cos(2*pi*n*x/L)/sqrt(L) on abs(x)<=L/2; zero otherwise',sources=sources,pairs=pairs,pooled=dict(columns=32,weighting='Each physical column has unit L2 norm, equal weight; Gram matrix on R.',tolerance=fmt(tol),relative_singular_value_rank=relrank,absolute_singular_value_rank=absrank,uniform_column_L2_error_rank=uniformrank,RMS_column_L2_error_rank=frobrank,relative_rank_reconstruction=reconstruct[relrank],uniform_rank_reconstruction=reconstruct[uniformrank],singular_values=[fmt(s) for s in sing]),validation=dict(max_same_cell_orthogonality_error=fmt(max(orth)),analytic_vs_GL64_cross_20_24_max_error=fmt(quadrature_error),source_m24_100_vs_140_cross_max_error=fmt(high_error),gram_min_eigenvalue=fmt(min(raw)),pooled_trace=fmt(mp.trace(G)) if hasattr(mp,'trace') else fmt(sum(G[i,i] for i in range(32)))))
 (OUT/'limit.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(dict(pairs=[dict(m=r['m'],m_prime=r['m_prime'],diagonal_overlaps=r['diagonal_overlaps'],max_angles=[s['max_angle_degrees'] for s in r['subspaces'] if s['dimension'] in (4,6,8)]) for r in pairs],pooled=result['pooled'],validation=result['validation']),indent=2))
if __name__=='__main__':main()
