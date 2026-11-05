// Vasyunin autocorrelation: BDBLS arXiv:math/0306251 Prop.89;
// Bettin-Conrey arXiv:1111.0931 eq.(13). Diagnostic arithmetic, not intervals.
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <vector>
#include <omp.h>
int main(int argc,char**argv){
 if(argc!=3)return 2;int N=std::stoi(argv[1]);if(N<2||N>5000)return 3;
 const long double pi=acosl(-1.L),kap=logl(2*pi)-0.577215664901532860606512090082402431L;
 std::vector<std::vector<long double>> V(N+1);for(int q=1;q<=N;q++)V[q].resize(q,0);
 std::atomic<unsigned long long> done(0);long double total=(long double)N*(N+1)*(2*N+1)/6-1;
 auto start=std::chrono::steady_clock::now();
 #pragma omp parallel for schedule(dynamic,1)
 for(int q=2;q<=N;q++){
  int half=(q-1)/2;std::vector<long double> cot(half+1);
  for(int j=1;j<=half;j++)cot[j]=1/tanl(pi*j/q);
  for(int h=1;2*h<q;h++)if(std::gcd(h,q)==1){
   long double sum=0;int rem=h;
   for(int j=1;j<=half;j++){sum+=(2.L*rem/q-1)*cot[j];rem+=h;if(rem>=q)rem-=q;}
   V[q][h]=sum;V[q][q-h]=-sum;
  }
  auto d=done.fetch_add((unsigned long long)q*q)+(unsigned long long)q*q;
  if(q%100==0||q==N){
   #pragma omp critical
   {double f=std::min(1.L,d/total),sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();int bars=(int)(30*f);
    std::cout<<'['<<std::string(bars,'#')<<std::string(30-bars,'.')<<"] "<<std::fixed<<std::setprecision(1)<<100*f<<"% ETA "<<(f>0?sec*(1-f)/f:0)<<"s cotangent rows\n"<<std::flush;}
  }
 }
 auto Q=[&](int n,int m){int g=std::gcd(n,m),h=n/g,k=m/g;
  long double v1=k==1?0:V[k][h%k],v2=h==1?0:V[h][k%h];
  return (kap*(1.L/h+1.L/k)/2+(k-h)*logl((long double)h/k)/(2.L*h*k)-pi*(v1+v2)/(2.L*h*k))/g;
 };
 std::vector<long double> q1(N+1);for(int n=1;n<=N;n++)q1[n]=Q(n,1);
 std::vector<double> G((size_t)(N-1)*(N-1));
 #pragma omp parallel for schedule(static)
 for(int n=2;n<=N;n++)for(int m=2;m<=n;m++){
  double x=(double)(Q(n,m)-q1[n]/m-q1[m]/n+kap/((long double)n*m));
  G[(size_t)(n-2)*(N-1)+m-2]=x;G[(size_t)(m-2)*(N-1)+n-2]=x;
 }
 std::cout<<"[##############################] 100.0% ETA 0s cotangent rows\n";
 std::ofstream f(argv[2],std::ios::binary);uint32_t d=N-1;f.write((char*)&d,4);f.write((char*)G.data(),G.size()*8);for(int n=0;n<=N;n++){double v=(double)q1[n];f.write((char*)&v,8);}if(!f)return 4;
 std::cout<<"native_N="<<N<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<" long_double_digits="<<__LDBL_MANT_DIG__<<"\n";
}
