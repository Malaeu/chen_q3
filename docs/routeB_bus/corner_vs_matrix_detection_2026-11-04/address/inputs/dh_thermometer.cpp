// Own DH source only. 192-bit MPFR convolution, extended-precision streaming diagnostic.
#include <mpfr.h>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <vector>
#include <string>
#include "dh_constants.h"
constexpr mpfr_rnd_t R=MPFR_RNDN;constexpr int BITS=192;
struct Num{mpfr_t v;Num(){mpfr_init2(v,BITS);mpfr_set_zero(v,0);}~Num(){mpfr_clear(v);}Num(const Num&)=delete;Num&operator=(const Num&)=delete;};
struct Kahan{long double s=0,c=0;void add(long double x){long double y=x-c,t=s+y;c=(t-s)-y;s=t;}};
std::string dec(mpfr_srcptr x){char b[160];mpfr_snprintf(b,sizeof(b),"%.65Rg",x);return b;}
long double tail(long double m){long double x=1/(m*m),power=1,sum=0;int K=m<64?32:4;for(int r=0;r<K;r++){long double a=2*r+1.5L;sum+=power/(a*a);power*=x;}return sum/(m*sqrtl(m));}
int main(int argc,char**argv){if(argc<4)return 2;const uint32_t N=10000000;std::string out=argv[1];auto start=std::chrono::steady_clock::now();
 std::vector<uint32_t>spf(N+1,0);for(uint32_t p=2;(uint64_t)p*p<=N;p++)if(!spf[p])for(uint32_t n=p*p;n<=N;n+=p)if(!spf[n])spf[n]=p;
 std::vector<Num>logs(N+1),b(N+1);Num tau,u,v,btau,w,root,s1,s2,work,minS1,minS2,minL;mpfr_set_ui(u.v,5,R);mpfr_sqrt(u.v,u.v,R);mpfr_mul_ui(v.v,u.v,2,R);mpfr_ui_sub(v.v,10,v.v,R);mpfr_sqrt(v.v,v.v,R);mpfr_sub_ui(v.v,v.v,2,R);mpfr_sub_ui(u.v,u.v,1,R);mpfr_div(tau.v,v.v,u.v,R);
 for(uint32_t n=2;n<=N;n++){if(!spf[n]){mpfr_set_ui(logs[n].v,n,R);mpfr_log(logs[n].v,logs[n].v,R);}else mpfr_add(logs[n].v,logs[n/spf[n]].v,logs[spf[n]].v,R);
  switch(n%5){case 1:mpfr_set(b[n].v,logs[n].v,R);break;case 2:mpfr_mul(b[n].v,tau.v,logs[n].v,R);break;case 3:mpfr_mul(b[n].v,tau.v,logs[n].v,R);mpfr_neg(b[n].v,b[n].v,R);break;case 4:mpfr_neg(b[n].v,logs[n].v,R);break;}}
 std::cout<<"initialized seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
 for(uint32_t d=2;d<=N/2;d++){if(mpfr_zero_p(b[d].v))continue;mpfr_mul(btau.v,b[d].v,tau.v,R);for(uint32_t k=2;k<=N/d;k++){uint32_t n=d*k;switch(k%5){case 1:mpfr_sub(b[n].v,b[n].v,b[d].v,R);break;case 2:mpfr_sub(b[n].v,b[n].v,btau.v,R);break;case 3:mpfr_add(b[n].v,b[n].v,btau.v,R);break;case 4:mpfr_add(b[n].v,b[n].v,b[d].v,R);break;}}}
 std::cout<<"convolution done seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
 std::ofstream coeff(argv[2],std::ios::binary),raw(argv[3],std::ios::binary),cp(out+"/ADD_DH_CHECKPOINT_SUMS.csv"),rec(out+"/ADD_DH_RECORD_MINIMA.csv"),spots(out+"/ADD_DH_COEFFICIENT_SPOTS.csv");
 cp<<"kind,m,S1_mp192,S2_mp192,Psi_native\n"<<std::setprecision(23);rec<<"m,log_m,Psi\n"<<std::setprecision(23);spots<<"n,b_mp192\n";std::vector<uint32_t>checks={2,3,4,6,10,16,40,75,80,160,300,1000,2000,10000,100000,1000000,N};size_t ic=0;Kahan ns1,ns2;long double mn=1e99L,mx=-1e99L;uint32_t mnm=0,mxm=0,first=0;uint64_t countrec=0,negative=0;std::vector<double>buf;buf.reserve(8192);
 for(uint32_t m=2;m<=N;m++){long double L=logl((long double)m),psi=DH_SLOPE*L+DH_CONST-tail(m)-L*ns1.s+ns2.s;if(!std::isfinite(psi))return 4;
  if(psi<mn){mn=psi;mnm=m;countrec++;rec<<m<<','<<L<<','<<psi<<'\n';mpfr_set(minS1.v,s1.v,R);mpfr_set(minS2.v,s2.v,R);mpfr_set(minL.v,logs[m].v,R);}if(psi>mx){mx=psi;mxm=m;}if(psi<0){negative++;if(!first){first=m;cp<<"first_negative,"<<m<<','<<dec(s1.v)<<','<<dec(s2.v)<<','<<psi<<'\n';}}
  if(ic<checks.size()&&m==checks[ic]){cp<<"checkpoint,"<<m<<','<<dec(s1.v)<<','<<dec(s2.v)<<','<<psi<<'\n';ic++;spots<<m<<','<<dec(b[m].v)<<'\n';}
  double bd=mpfr_get_d(b[m].v,R);coeff.write((char*)&bd,8);buf.push_back((double)psi);if(buf.size()==8192){raw.write((char*)buf.data(),buf.size()*8);buf.clear();}
  mpfr_set_ui(root.v,m,R);mpfr_sqrt(root.v,root.v,R);mpfr_div(w.v,b[m].v,root.v,R);long double nw=mpfr_get_ld(w.v,R);ns1.add(nw);ns2.add(nw*L);mpfr_add(s1.v,s1.v,w.v,R);mpfr_mul(work.v,w.v,logs[m].v,R);mpfr_add(s2.v,s2.v,work.v,R);
  if(m%1000000==0)std::cout<<"m="<<m<<" firstnegative="<<first<<" min="<<std::setprecision(18)<<mn<<" at="<<mnm<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
 }
 if(!buf.empty()){raw.write((char*)buf.data(),buf.size()*8);}cp<<"minimum,"<<mnm<<','<<dec(minS1.v)<<','<<dec(minS2.v)<<','<<mn<<'\n';
 std::ofstream j(out+"/ADD_DH_SUMMARY.json");j<<std::setprecision(23)<<"{\n\"world\":\"DH own conductor5 oddGamma no pole\",\n\"max_m\":"<<N<<",\n\"evaluated_integers\":"<<N-1<<",\n\"coefficient_bits\":"<<BITS<<",\n\"long_double_mantissa_bits\":64,\n\"first_negative_m\":"<<first<<",\n\"negative_count\":"<<negative<<",\n\"minimum_m\":"<<mnm<<",\n\"minimum_native\":\""<<mn<<"\",\n\"maximum_m\":"<<mxm<<",\n\"maximum_native\":\""<<mx<<"\",\n\"record_count\":"<<countrec<<",\n\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n}\n";
}
