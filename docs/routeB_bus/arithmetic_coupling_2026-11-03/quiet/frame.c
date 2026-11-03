/* Ordered twice-reorthogonalized MPFR MGS. No rank decision from float data. */
#include <stdlib.h>
#include <math.h>
#include <gmp.h>
/* Public MPFR ABI types, matching MPFR 4.x on this Linux x86_64 build. */
typedef long mpfr_prec_t; typedef long mpfr_exp_t;
typedef struct { mpfr_prec_t _mpfr_prec; int _mpfr_sign; mpfr_exp_t _mpfr_exp; mp_limb_t *_mpfr_d; } mfr;
extern void mpfr_init2(mfr*,long); extern void mpfr_clear(mfr*);
extern int mpfr_set_str(mfr*,const char*,int,int); extern int mpfr_dot(mfr*,mfr**,mfr**,unsigned long,int);
extern int mpfr_sqrt(mfr*,const mfr*,int); extern int mpfr_div(mfr*,const mfr*,const mfr*,int);
extern int mpfr_neg(mfr*,const mfr*,int); extern int mpfr_fma(mfr*,const mfr*,const mfr*,const mfr*,int);
extern int mpfr_zero_p(const mfr*); extern double mpfr_get_d(const mfr*,int);
extern int mpfr_set(mfr*,const mfr*,int); extern int mpfr_set_ui(mfr*,unsigned long,int);
extern int mpfr_add(mfr*,const mfr*,const mfr*,int); extern int mpfr_sub(mfr*,const mfr*,const mfr*,int); extern int mpfr_mul(mfr*,const mfr*,const mfr*,int);
int shifted_ldl(int n,long bits,const char **data,int shifts,const char **ss,int *negative) {
 mfr *a=calloc((size_t)n*n,sizeof(mfr)),*l=calloc((size_t)n*n,sizeof(mfr)),*x=calloc((size_t)n*n,sizeof(mfr)),*d=calloc(n,sizeof(mfr));
 mfr alpha,shift;mpfr_init2(&alpha,bits);mpfr_init2(&shift,bits);
 mfr **u=malloc(n*sizeof(mfr*)),**v=malloc(n*sizeof(mfr*));
 for(int k=0;k<n*n;k++){mpfr_init2(a+k,bits);mpfr_init2(l+k,bits);mpfr_init2(x+k,bits);if(mpfr_set_str(a+k,data[k],10,0))return -2;}
 for(int k=0;k<n;k++)mpfr_init2(d+k,bits);
 int status=0;
 for(int s=0;s<shifts;s++){
  mpfr_set_str(&shift,ss[s],10,0);negative[s]=0;
  for(int i=0;i<n;i++){
   for(int k=0;k<i;k++)u[k]=x+i*n+k;
   for(int j=0;j<i;j++){
    for(int k=0;k<j;k++)v[k]=l+j*n+k;
    if(j)mpfr_dot(&alpha,u,v,j,0);else mpfr_set_ui(&alpha,0,0);
    mpfr_sub(&alpha,a+i*n+j,&alpha,0);mpfr_div(l+i*n+j,&alpha,d+j,0);mpfr_mul(x+i*n+j,l+i*n+j,d+j,0);
   }
   for(int k=0;k<i;k++)v[k]=l+i*n+k;
   if(i)mpfr_dot(&alpha,u,v,i,0);else mpfr_set_ui(&alpha,0,0);
   mpfr_add(d+i,a+i*n+i,&shift,0);mpfr_sub(d+i,d+i,&alpha,0);
   if(mpfr_zero_p(d+i)){status=-1;goto cleanup;}
   if(d[i]._mpfr_sign<0)negative[s]++;
  }
 }
cleanup:
 for(int k=0;k<n*n;k++){mpfr_clear(a+k);mpfr_clear(l+k);mpfr_clear(x+k);}for(int k=0;k<n;k++)mpfr_clear(d+k);
 mpfr_clear(&alpha);mpfr_clear(&shift);free(a);free(l);free(x);free(d);free(u);free(v);return status;
}
int frame_mgs(int nr,int nc,long bits,const char **data,double *out,double *ratios) {
 mfr *a=calloc((size_t)nr*nc,sizeof(mfr)),norm,alpha,norm0;
 mfr **v=malloc(nc*sizeof(mfr*)),**u=malloc(nc*sizeof(mfr*));
 mpfr_init2(&norm,bits);mpfr_init2(&alpha,bits);mpfr_init2(&norm0,bits);
 for(int k=0;k<nr*nc;k++){mpfr_init2(a+k,bits);if(mpfr_set_str(a+k,data[k],10,0))return -2;}
 int status=0;
 for(int i=0;i<nr;i++) {
  for(int j=0;j<nc;j++)v[j]=a+i*nc+j;
  mpfr_dot(&norm0,v,v,nc,0);mpfr_sqrt(&norm0,&norm0,0);
  for(int repeat=0;repeat<2;repeat++)for(int k=0;k<i;k++) {
   for(int j=0;j<nc;j++)u[j]=a+k*nc+j;
   mpfr_dot(&alpha,v,u,nc,0);mpfr_neg(&alpha,&alpha,0);
   for(int j=0;j<nc;j++)mpfr_fma(v[j],&alpha,u[j],v[j],0);
  }
  mpfr_dot(&norm,v,v,nc,0);mpfr_sqrt(&norm,&norm,0);
  if(mpfr_zero_p(&norm)){status=-1;break;}
  mpfr_div(&alpha,&norm,&norm0,0);ratios[i]=mpfr_get_d(&alpha,0);
  for(int j=0;j<nc;j++){mpfr_div(v[j],v[j],&norm,0);out[i*nc+j]=mpfr_get_d(v[j],0);}
 }
 for(int k=0;k<nr*nc;k++)mpfr_clear(a+k);
 mpfr_clear(&norm);mpfr_clear(&alpha);mpfr_clear(&norm0);free(a);free(v);free(u);return status;
}
