// Native literal inverse forms; GMP mpf, no double precision in the solve.
// DIAGNOSTIC_NEVER_A_PROOF. LDL inertia is numerical, not interval-certified.
#include <gmpxx.h>
#include <vector>
#include <iostream>
#include <iomanip>
#include <string>
using R=mpf_class; using V=std::vector<R>;
struct M{int n,m;V a;M(int n_,int m_):n(n_),m(m_),a(n_*m_){} R& operator()(int i,int j){return a[i*m+j];}const R& operator()(int i,int j)const{return a[i*m+j];}};
R ab(const R& x){return x<0?-x:x;} R dot(const V& a,const V& b){R x=0;for(size_t i=0;i<a.size();++i)x+=a[i]*b[i];return x;}
int main(int argc,char**argv){
 int bits=argc>1?std::stoi(argv[1]):768;mpf_set_default_prec(bits);
 int m,q,J,K,ispole; if(!(std::cin>>m>>q>>J>>K>>ispole))return 2;int d=m+1;
 R L,sqrtL,invpi,s2,om2,c,twotail;std::cin>>L>>sqrtL>>invpi>>s2>>om2>>c>>twotail;
 V sm(d),di(d),ps(d),pd(d),ds(d);for(int n=0;n<d;++n)ds[n]=n?s2:R(1);
 for(int k=0;k<J;++k){R y,co,si,wt;std::cin>>y>>co>>si>>wt;R cn=1,sn=0;
  for(int n=0;n<d;++n){sm[n]+=wt*sn;R sp=0;if(n)sp=sn*invpi/n;di[n]+=wt*(2*y+2*(1-y)*(1-cn)+sp);R v=cn*co-sn*si;sn=sn*co+cn*si;cn=v;}}
 for(int k=0;k<K;++k){R y,co,si,wt;std::cin>>y>>co>>si>>wt;R cn=1,sn=0;
  for(int n=0;n<d;++n){ps[n]+=wt*sn;R sp=0;if(n)sp=sn*invpi/n;pd[n]+=wt*(2*(1-y)*cn-sp);R v=cn*co-sn*si;sn=sn*co+cn*si;cn=v;}}
 V pole(d);for(auto&x:pole)std::cin>>x;M A(d,d);
 for(int i=0;i<d;++i){A(i,i)=c+di[i]+twotail-pd[i];for(int j=i+1;j<d;++j){R x=ds[i]*ds[j]*invpi*(i*(sm[i]+ps[i])-j*(sm[j]+ps[j]))/(i*i-j*j);A(i,j)=x;A(j,i)=x;}}
 if(ispole)for(int i=0;i<d;++i)for(int j=0;j<d;++j)A(i,j)+=pole[i]*pole[j];
 M U(d,q);R minrow=1,maxorth=0;
 for(int k=0;k<q;++k){int kind;R zr,zi,ar,ai;std::cin>>kind>>zr>>zi>>ar>>ai;V v(d);
  for(int n=0;n<d;++n){R den=zr-om2*n*n;if(kind==0)v[n]=ds[n]*ar/den;else{R den2=den*den+zi*zi;v[n]=s2*ds[n]*(kind==1?R(ar*den+ai*zi):R(ai*den-ar*zi))/den2;}}
  R norm=sqrt(dot(v,v));if(norm==0)return 3;for(auto&x:v)x/=norm;
  for(int pass=0;pass<2;++pass)for(int j=0;j<k;++j){R proj=0;for(int n=0;n<d;++n)proj+=U(n,j)*v[n];for(int n=0;n<d;++n)v[n]-=proj*U(n,j);}
  norm=sqrt(dot(v,v));if(norm==0)return 4;if(norm<minrow)minrow=norm;for(int n=0;n<d;++n)U(n,k)=v[n]/norm;
 }
 for(int i=0;i<q;++i)for(int j=0;j<=i;++j){R a=0;for(int n=0;n<d;++n)a+=U(n,i)*U(n,j);if(i==j)a-=1;if(ab(a)>maxorth)maxorth=ab(a);}
 M B(d,q),C(q,q);for(int n=0;n<d;++n)for(int j=0;j<q;++j){R a=0;for(int k=0;k<d;++k)a+=A(n,k)*U(k,j);B(n,j)=a;}
 R scale=0;for(int i=0;i<q;++i)for(int j=0;j<=i;++j){R a=0;for(int n=0;n<d;++n)a+=U(n,i)*B(n,j);C(i,j)=a;C(j,i)=a;if(ab(a)>scale)scale=ab(a);}
 M LL(q,q);V dd(q);int neg=0;R minp=scale;for(int j=0;j<q;++j){R pivot=C(j,j);for(int k=0;k<j;++k)pivot-=LL(j,k)*LL(j,k)*dd[k];if(pivot==0)return 5;dd[j]=pivot;LL(j,j)=1;if(pivot<0)++neg;if(ab(pivot)<minp)minp=ab(pivot);
  for(int i=j+1;i<q;++i){R a=C(i,j);for(int k=0;k<j;++k)a-=LL(i,k)*LL(j,k)*dd[k];LL(i,j)=a/pivot;}}
 M queries(d,4);for(int n=0;n<d;++n)for(int j=0;j<4;++j)std::cin>>queries(n,j);
 V kval(4),cross(4);M rhs(q,4),sol(q,4);R maxres=0;
 for(int j=0;j<4;++j){V b(q),y(q),x(q);for(int k=0;k<q;++k){for(int n=0;n<d;++n)b[k]+=U(n,k)*queries(n,j);rhs(k,j)=b[k];}
  for(int i=0;i<q;++i){y[i]=b[i];for(int k=0;k<i;++k)y[i]-=LL(i,k)*y[k];x[i]=y[i]/dd[i];}
  for(int i=q-1;i>=0;--i){for(int k=i+1;k<q;++k)x[i]-=LL(k,i)*x[k];sol(i,j)=x[i];}kval[j]=dot(b,x);
  R rn=0,bn=0,xn=0;for(int i=0;i<q;++i){R a=-b[i];for(int k=0;k<q;++k)a+=C(i,k)*x[k];rn+=a*a;bn+=b[i]*b[i];xn+=x[i]*x[i];}R rel=sqrt(rn)/(sqrt(bn)+scale*q*sqrt(xn));if(rel>maxres)maxres=rel;
 }
 for(int j=0;j<4;++j)for(int i=0;i<q;++i)cross[j]+=rhs(i,0)*sol(i,j);
 V probe(d);R pn=0,pr=0;for(int n=0;n<d;++n){probe[n]=R(n%2?-1:1)/(n+1);pn+=probe[n]*probe[n];}for(int i=0;i<d;++i)for(int j=0;j<d;++j)pr+=probe[i]*A(i,j)*probe[j];pr/=pn;
 std::cout<<std::scientific<<std::setprecision(100);
 std::cout<<"{\"m\":"<<m<<",\"q\":"<<q<<",\"bits\":"<<bits<<",\"negative_pivots\":"<<neg<<",\"positive_pivots\":"<<q-neg<<",\"min_pivot_over_C_scale\":\""<<minp/scale<<"\",\"minimum_MGS_norm\":\""<<minrow<<"\",\"U_orthogonality_max\":\""<<maxorth<<"\",\"relative_solve_residual\":\""<<maxres<<"\",\"source_probe_Rayleigh\":\""<<pr<<"\",\"K\":[";
 for(int j=0;j<4;++j)std::cout<<(j?",":"")<<"\""<<kval[j]<<"\"";std::cout<<"],\"endpoint_cross\":[";for(int j=0;j<4;++j)std::cout<<(j?",":"")<<"\""<<cross[j]<<"\"";std::cout<<"]}\n";
}
