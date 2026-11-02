"""Zero-space mixing and carrier comparison; DIAGNOSTIC_NEVER_A_PROOF."""
from pathlib import Path
import json,csv,math
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
mp.mp.dps=180
def fmt(x):return mp.nstr(x,100)
def save(name,rows):
 with (P/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def angle(X,Y):
 s=mp.svd(X.T*Y,compute_uv=False);return mp.acos(min(mp.mpf(1),max(mp.mpf(0),min(s))))*180/mp.pi
def main():
 zeros=[mp.mpf(r['gamma']) for r in csv.DictReader((P/'zeros.csv').open()) if mp.mpf(r['gamma'])<=400]
 levels=[];kernel=[];components=[];subspaces=[];prefixmix=[];checks=[]
 fig,axs=plt.subplots(2,2,figsize=(13,10),constrained_layout=True)
 for col,m in enumerate((16,24)):
  data=json.loads((P/f'cell_m{m}.json').read_text());E=mp.matrix(data['E']);G=mp.matrix(data['G']);A=mp.matrix(data['A']);V=mp.matrix(data['V']);U=mp.matrix(data['U']);W=mp.matrix(data['W'])
  g=list(map(mp.mpf,data['G_eigenvalues']));ae=list(map(mp.mpf,data['A_eigenvalues']));p=E.rows;d=E.cols
  C=E*E.T;corr=np.empty((p,p));weights=np.empty((p,d))
  for j in range(p):
   for k in range(p):corr[j,k]=float(abs(C[j,k])/mp.sqrt(C[j,j]*C[k,k]))
   for i in range(d):weights[j,i]=float(W[j,i]**2)
   for k in range(j,min(p,j+5)):
    kernel.append(dict(m=m,j=j+1,k=k+1,gamma_j=fmt(zeros[j]),gamma_k=fmt(zeros[k]),C_jk=fmt(C[j,k]),normalized_signed_kernel=fmt(C[j,k]/mp.sqrt(C[j,j]*C[k,k])),absolute_correlation=corr[j,k]))
  omega=2*mp.pi*m/mp.log(m);neighbor={'below':[],'above':[],'above200':[]}
  for j in range(p-1):
   if zeros[j+1]<=omega:neighbor['below'].append(corr[j,j+1])
   if zeros[j]>omega:neighbor['above'].append(corr[j,j+1])
   if zeros[j]>200:neighbor['above200'].append(corr[j,j+1])
  re,R=mp.eigsy(A-2*G);boundary=mp.matrix([1]+[mp.sqrt(2)]*m);boundary/=mp.norm(boundary)
  check=dict(m=m,positive_zeros=p,carrier_dimension=d,C_forced_nullity_lower_bound=p-d,C_W_eigen_residual=fmt(mp.norm(C*W-W*mp.diag(g))),W_orthogonality_residual=fmt(mp.norm(W.T*W-mp.eye(d))),C_trace_minus_G_trace=fmt(mp.fsum(C[k,k] for k in range(p))-mp.fsum(G[i,i] for i in range(d))),tail_norm=fmt(re[d-1]),tail_second_eigenvalue=fmt(re[d-2]),tail_second_over_first=fmt(re[d-2]/re[d-1]),tail_top_boundary_overlap_squared=fmt(mp.fdot(R[:,d-1],boundary)**2),adjacent_row_correlation={k:dict(count=len(v),median=float(np.median(v)),minimum=min(v),maximum=max(v)) for k,v in neighbor.items()})
  checks.append(check)
  for i in range(d):
   w=weights[:,i];w=w/w.sum();peak=int(np.argmax(w));order=np.argsort(-w)
   # Shortest contiguous zero-index window containing at least90% of mass.
   best=(p+1,0,p-1);right=0;mass=0.
   for left in range(p):
    while right<p and mass<.9:mass+=w[right];right+=1
    if mass>=.9 and right-left<best[0]:best=(right-left,left,right-1)
    mass-=w[left]
   mean=sum(w[k]*float(zeros[k]) for k in range(p));sd=math.sqrt(sum(w[k]*(float(zeros[k])-mean)**2 for k in range(p)))
   ov=[mp.fdot(V[:,j],U[:,i])**2 for j in range(d)];jmax=max(range(d),key=lambda j:ov[j])
   row=dict(m=m,i=i,A_eigenvalue=fmt(ae[i]),G_eigenvalue=fmt(g[i]),twice_G_over_A=fmt(2*g[i]/ae[i]),same_index_carrier_overlap_squared=fmt(ov[i]),best_A_index=jmax,best_A_overlap_squared=fmt(ov[jmax]),zero_participation=1/float(np.sum(w*w)),maximum_zero_weight=float(w[peak]),peak_zero_index=peak+1,peak_gamma=fmt(zeros[peak]),mass_in_peak_and_two_neighbors=float(w[max(0,peak-1):min(p,peak+2)].sum()),window90_count=best[0],window90_first_zero=best[1]+1,window90_last_zero=best[2]+1,window90_first_gamma=fmt(zeros[best[1]]),window90_last_gamma=fmt(zeros[best[2]]),weighted_mean_gamma=mean,weighted_sd_gamma=sd,top_five_zero_indices=','.join(str(k+1) for k in order[:5]),top_five_weights=','.join(format(w[k],'.12g') for k in order[:5]))
   levels.append(row)
   for k in range(p):components.append(dict(m=m,i=i,k=k+1,gamma=fmt(zeros[k]),W_component=fmt(W[k,i]),squared_weight=fmt(W[k,i]**2)))
  for B in (2,4,8):
   r=sum(abs(x)<mp.mpf(m)**-B for x in ae);rg=sum(abs(2*x)<mp.mpf(m)**-B for x in g)
   subspaces.append(dict(m=m,B=B,A_cluster_count=r,twice_G_cluster_count=rg,maximum_principal_angle_degrees=fmt(angle(V[:,:r],U[:,:r]))))
  for q in data['prefixes']:
   if 'U' not in q:continue
   Uq=mp.matrix(q['U']);ov=U.T*Uq
   for i in range(d):prefixmix.append(dict(m=m,q=q['q'],height=q['height'],i=i,overlap_with_same_final_G_mode_squared=fmt(ov[i,i]**2),overlap_zero_padded_C_mode_with_final_squared=fmt(ov[i,i]**2*mp.mpf(q['g_eigenvalues'][i])/g[i]),best_final_G_mode=max(range(d),key=lambda j:abs(ov[j,i])),relative_eigenvalue_difference_from_400=q['relative_eigenvalue_difference_from_full'][i]))
  image=axs[0,col].imshow(np.log10(np.maximum(weights,1e-20)),origin='lower',aspect='auto',vmin=-8,vmax=0,cmap='viridis')
  axs[0,col].set(title=f'm={m}: zero-space eigenvectors of C',xlabel='Increasing G eigenmode i',ylabel='Zero index k (height labels)')
  ticks=[0,28,78,137,201];axs[0,col].set_yticks(ticks,[f'{k+1} (γ≈{float(zeros[k]):.0f})' for k in ticks]);fig.colorbar(image,ax=axs[0,col],label='log₁₀ |Wₖᵢ|²')
  image=axs[1,col].imshow(corr,origin='lower',extent=(.5,p+.5,.5,p+.5),vmin=0,vmax=1,cmap='magma');axs[1,col].set(title=f'm={m}: normalized kernel |Cⱼₖ|/√(CⱼⱼCₖₖ)',xlabel='Zero index k (1-based)',ylabel='Zero index j (1-based)');fig.colorbar(image,ax=axs[1,col])
  print('mixed',m,flush=True)
 fig.suptitle('Capacity matrices through height400 · positive-zero rows · DIAGNOSTIC_NEVER_A_PROOF')
 fig.savefig(P/'zero_mixing.svg');fig.savefig(P/'zero_mixing.png',dpi=150);plt.close(fig)
 save('levels.csv',levels);save('nearby_kernel.csv',kernel);save('zero_components.csv',components);save('subspaces.csv',subspaces);save('prefix_mixing.csv',prefixmix)
 (P/'mixing_checks.json').write_text(json.dumps(checks,indent=2)+'\n')
if __name__=='__main__':main()
