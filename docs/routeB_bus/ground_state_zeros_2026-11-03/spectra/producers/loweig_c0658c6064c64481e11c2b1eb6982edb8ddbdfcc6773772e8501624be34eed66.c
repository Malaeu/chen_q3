/* MPFR symmetric Householder, Sturm bisection, and inverse iteration.
 * Empirical arithmetic diagnostic: no outward interval certificate. */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <mpfr.h>
#define R MPFR_RNDN
static int n,bits; static mpfr_t *A,*d,*b,*tau,*work,*vv,*yy,*diag,*rhs;static mpfr_t t,u,s,alpha,norm,tmp,pivot,eps;
#define MAT(i,j) A[(i)*n+(j)]
static mpfr_t *arr(int n0){mpfr_t *a=malloc(sizeof(mpfr_t)*n0);for(int i=0;i<n0;i++)mpfr_init2(a[i],bits);return a;}
static void normvec(mpfr_t *v){mpfr_set_zero(s,0);for(int i=0;i<n;i++)mpfr_fma(s,v[i],v[i],s,R);mpfr_sqrt(s,s,R);for(int i=0;i<n;i++)mpfr_div(v[i],v[i],s,R);}
static int count(mpfr_t x){int c=0;mpfr_sub(pivot,d[0],x,R);for(int i=0;i<n;i++){if(i){mpfr_sqr(t,b[i-1],R);mpfr_div(t,t,pivot,R);mpfr_sub(pivot,d[i],x,R);mpfr_sub(pivot,pivot,t,R);}if(mpfr_zero_p(pivot))mpfr_neg(pivot,eps,R);if(mpfr_sgn(pivot)<0)c++;}return c;}
int main(){if(scanf("%d %d",&n,&bits)!=2)return 1;mpfr_set_default_prec(bits);A=arr(n*n);d=arr(n);b=arr(n);tau=arr(n);work=arr(n);vv=arr(n);yy=arr(n);diag=arr(n);rhs=arr(n);mpfr_inits(t,u,s,alpha,norm,tmp,pivot,eps,(mpfr_ptr)0);mpfr_set_ui_2exp(eps,1,-bits+16,R);for(int i=0;i<n*n;i++)if(!mpfr_inp_str(A[i],stdin,0,R))return 2;
clock_t st=clock();
for(int k=0;k<n-2;k++){
 mpfr_set(d[k],MAT(k,k),R);mpfr_set_zero(norm,0);for(int i=k+1;i<n;i++)mpfr_fma(norm,MAT(k,i),MAT(k,i),norm,R);mpfr_sqrt(norm,norm,R);if(mpfr_zero_p(norm)){mpfr_set_zero(b[k],0);mpfr_set_zero(tau[k],0);continue;}
 mpfr_set(alpha,norm,R);if(mpfr_sgn(MAT(k,k+1))>=0)mpfr_neg(alpha,alpha,R);mpfr_set(b[k],alpha,R);mpfr_sub(tmp,MAT(k,k+1),alpha,R);mpfr_set_ui(MAT(k+1,k),1,R);for(int i=k+2;i<n;i++)mpfr_div(MAT(i,k),MAT(k,i),tmp,R);
 mpfr_set_ui(s,1,R);for(int i=k+2;i<n;i++)mpfr_fma(s,MAT(i,k),MAT(i,k),s,R);mpfr_ui_div(tau[k],2,s,R);
 for(int i=k+1;i<n;i++){mpfr_set_zero(work[i],0);for(int j=k+1;j<n;j++)mpfr_fma(work[i],MAT((i<j?i:j),(i<j?j:i)),MAT(j,k),work[i],R);mpfr_mul(work[i],work[i],tau[k],R);}
 mpfr_set_zero(s,0);for(int i=k+1;i<n;i++)mpfr_fma(s,MAT(i,k),work[i],s,R);mpfr_mul(s,s,tau[k],R);mpfr_div_ui(s,s,2,R);for(int i=k+1;i<n;i++){mpfr_mul(t,s,MAT(i,k),R);mpfr_sub(work[i],work[i],t,R);}
 for(int i=k+1;i<n;i++)for(int j=i;j<n;j++){mpfr_mul(t,MAT(i,k),work[j],R);mpfr_fma(t,work[i],MAT(j,k),t,R);mpfr_sub(MAT(i,j),MAT(i,j),t,R);}
}
mpfr_set(d[n-2],MAT(n-2,n-2),R);mpfr_set(d[n-1],MAT(n-1,n-1),R);mpfr_set(b[n-2],MAT(n-2,n-1),R);
clock_t reduced=clock(); double eigsecs[2]; int bisiters[2];
mpfr_t lo,hi,left,right,mid,scale,lambda[2],width[2],shift;mpfr_inits(lo,hi,left,right,mid,scale,shift,(mpfr_ptr)0);for(int k=0;k<2;k++){mpfr_init2(lambda[k],bits);mpfr_init2(width[k],bits);}mpfr_set_inf(lo,1);mpfr_set_inf(hi,-1);mpfr_set_ui(scale,1,R);
for(int i=0;i<n;i++){mpfr_set_zero(s,0);if(i)mpfr_abs(s,b[i-1],R);if(i<n-1){mpfr_abs(t,b[i],R);mpfr_add(s,s,t,R);}mpfr_sub(t,d[i],s,R);if(mpfr_less_p(t,lo))mpfr_set(lo,t,R);mpfr_add(t,d[i],s,R);if(mpfr_greater_p(t,hi))mpfr_set(hi,t,R);mpfr_abs(t,d[i],R);mpfr_add(t,t,s,R);if(mpfr_greater_p(t,scale))mpfr_set(scale,t,R);}
mpfr_mul(eps,eps,scale,R);mpfr_sub(lo,lo,eps,R);mpfr_add(hi,hi,eps,R);
mpfr_t *evec[2];evec[0]=arr(n);evec[1]=arr(n);
for(int kth=0;kth<2;kth++){
 clock_t eigstart=clock();
 mpfr_set(left,lo,R);mpfr_set(right,hi,R);int iter=0;
 while(1){mpfr_add(mid,left,right,R);mpfr_div_ui(mid,mid,2,R);int c=count(mid);if(c<=kth)mpfr_set(left,mid,R);else mpfr_set(right,mid,R);mpfr_sub(t,right,left,R);if(mpfr_lessequal_p(t,eps)||++iter>bits+64)break;}
 bisiters[kth]=iter;mpfr_add(lambda[kth],left,right,R);mpfr_div_ui(lambda[kth],lambda[kth],2,R);mpfr_sub(width[kth],right,left,R);mpfr_sub(shift,lambda[kth],eps,R);
 for(int i=0;i<n;i++)mpfr_set_ui(vv[i],1+(i%7),R);normvec(vv);
 for(int it=0;it<4;it++){
  mpfr_sub(diag[0],d[0],shift,R);mpfr_set(rhs[0],vv[0],R);
  for(int i=1;i<n;i++){if(mpfr_zero_p(diag[i-1]))mpfr_set(diag[i-1],eps,R);mpfr_div(u,b[i-1],diag[i-1],R);mpfr_mul(t,u,b[i-1],R);mpfr_sub(diag[i],d[i],shift,R);mpfr_sub(diag[i],diag[i],t,R);mpfr_mul(t,u,rhs[i-1],R);mpfr_sub(rhs[i],vv[i],t,R);}
  if(mpfr_zero_p(diag[n-1]))mpfr_set(diag[n-1],eps,R);mpfr_div(yy[n-1],rhs[n-1],diag[n-1],R);for(int i=n-2;i>=0;i--){mpfr_mul(t,b[i],yy[i+1],R);mpfr_sub(t,rhs[i],t,R);mpfr_div(yy[i],t,diag[i],R);}normvec(yy);for(int i=0;i<n;i++)mpfr_set(vv[i],yy[i],R);
 }
 /* Return each tridiagonal vector through Q=H0 H1 ... */
 for(int k=n-3;k>=0;k--){mpfr_set_zero(s,0);for(int i=k+1;i<n;i++)mpfr_fma(s,MAT(i,k),vv[i],s,R);mpfr_mul(s,s,tau[k],R);for(int i=k+1;i<n;i++){mpfr_mul(t,s,MAT(i,k),R);mpfr_sub(vv[i],vv[i],t,R);}}
 normvec(vv);for(int i=0;i<n;i++)mpfr_set(evec[kth][i],vv[i],R);eigsecs[kth]=(double)(clock()-eigstart)/CLOCKS_PER_SEC;
}
int digits=(int)(bits*.30103)+3;printf("{\"tridiagonal_seconds\":%.9f,\"low_two_eigen_seconds\":[%.9f,%.9f],\"bisection_iterations\":[%d,%d],\"seconds\":%.9f,\"lambda\":[",(double)(reduced-st)/CLOCKS_PER_SEC,eigsecs[0],eigsecs[1],bisiters[0],bisiters[1],(double)(clock()-st)/CLOCKS_PER_SEC);for(int k=0;k<2;k++){if(k)printf(",");printf("\"");mpfr_out_str(stdout,10,digits,lambda[k],R);printf("\"");}printf("],\"bisection_width\":[");for(int k=0;k<2;k++){if(k)printf(",");printf("\"");mpfr_out_str(stdout,10,digits,width[k],R);printf("\"");}printf("],\"v\":[");for(int k=0;k<2;k++){if(k)printf(",");printf("[");for(int i=0;i<n;i++){if(i)printf(",");printf("\"");mpfr_out_str(stdout,10,digits,evec[k][i],R);printf("\"");}printf("]");}printf("]}\n");return 0;}
