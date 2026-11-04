// Exhaustive corner thermometer, diagnostic point arithmetic, never a proof.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <queue>
#include <string>
#include <vector>
#include "constants.h"
struct Kahan {long double sum=0,c=0;void add(long double x){long double y=x-c,t=sum+y;c=(t-sum)-y;sum=t;}};
struct Power {uint32_t n,p;};
struct Cell {uint32_t lo=0,hi=0,minm=0,maxm=0;long double low=1e9L,high=-1e9L;};
long double tail(long double m,bool primitive=false){long double x=1/(m*m),power=x,sum=0;int K=m<64?32:3;for(int r=1;r<=K;r++){long double den=4*r+1;sum+=power/(den*den*(primitive?den:1));power*=x;}return (primitive?8:4)*sum/sqrtl(m);}
long double value(uint32_t m,long double L,long double s1,long double s2){return ((4*sqrtl((long double)m)-L*s1)+s2)+ALPHA*L+CONSTC-tail(m);}
long double primitive(uint32_t m,long double L,long double s1,long double s2,long double s3){return 8*sqrtl((long double)m)+ALPHA*L*L/2+CONSTC*L-(L*L*s1-2*L*s2+s3)/2+tail(m,true);}
int main(int argc,char**argv){
 if(argc<4){std::cerr<<"usage: thermometer primes.bin output_dir local_values.bin\n";return 2;}const uint32_t M=100000000;std::string out=argv[2];
 auto start=std::chrono::steady_clock::now();std::ifstream f(argv[1],std::ios::binary|std::ios::ate);size_t count=f.tellg()/4;f.seekg(0);std::vector<uint32_t>primes(count);f.read((char*)primes.data(),count*4);if(count!=5761455||primes.front()!=2||primes.back()!=99999989){std::cerr<<"prime-file census mismatch";return 3;}
 std::vector<Power> powers;for(uint32_t p:primes){if((uint64_t)p*p>M)break;for(uint64_t n=(uint64_t)p*p;n<=M;){powers.push_back({(uint32_t)n,p});if(n>M/p)break;n*=p;}}
 std::sort(powers.begin(),powers.end(),[](Power a,Power b){return a.n<b.n;});
 std::ofstream cp(out+"/CHECKPOINTS_NATIVE.csv"),rec(out+"/RECORD_MINIMA.csv"),g1(out+"/G1_NATIVE.csv"),raw(argv[3],std::ios::binary);
 cp<<"m,Psi,S1,S2,S3,primitive\n";rec<<"m,log_m,Psi\n";g1<<"m,Psi,reference,abs_error,pass\n";cp<<std::setprecision(23);rec<<std::setprecision(23);g1<<std::setprecision(23);
 Kahan s1,s2,s3,mean,trap;long double minv=1e9L,maxv=-1e9L,min1000=1e9L,prev=0,prevL=0,lastF=0;uint32_t minm=0,maxm=0,min1000m=0,checkpoint=10;size_t ip=0,ipp=0;uint64_t records=0,nonpositive=0;const int NB=4000;std::vector<Cell>bins(NB);
 std::priority_queue<std::pair<long double,uint32_t>>top;std::vector<double>buf;buf.reserve(8192);long double L0=logl(2.L),LM=logl((long double)M),F2=primitive(2,L0,0,0,0);
 for(uint32_t m=2;m<=M;m++){
  long double L=logl((long double)m),v=value(m,L,s1.sum,s2.sum);if(!std::isfinite(v)){std::cerr<<"nonfinite";return 4;}
  if(m==16||m==80||m==300){long double ref=m==16?0.045942450631L:m==80?0.044990119994L:0.034530659232L;bool pass=fabsl(v-ref)<=1e-10L;g1<<m<<','<<v<<','<<ref<<','<<fabsl(v-ref)<<','<<pass<<'\n';g1.flush();if(!pass){std::cerr<<"G1 failed at"<<m;return 5;}}
  if(v<minv){minv=v;minm=m;rec<<m<<','<<L<<','<<v<<'\n';records++;}if(v>maxv){maxv=v;maxm=m;}if(m>=1000&&v<min1000){min1000=v;min1000m=m;}if(v<=0)nonpositive++;
  if(top.size()<20)top.push({v,m});else if(std::pair<long double,uint32_t>(v,m)<top.top()){top.pop();top.push({v,m});}
  mean.add(v);if(m>2)trap.add((v+prev)/2*(L-prevL));prev=v;prevL=L;
  int bin=std::min(NB-1,(int)((L-L0)/(LM-L0)*NB));auto &b=bins[bin];if(!b.lo)b.lo=m;b.hi=m;if(v<b.low){b.low=v;b.minm=m;}if(v>b.high){b.high=v;b.maxm=m;}
  buf.push_back((double)v);if(buf.size()==8192){raw.write((char*)buf.data(),buf.size()*sizeof(double));buf.clear();}
  if(m==checkpoint){lastF=primitive(m,L,s1.sum,s2.sum,s3.sum);cp<<m<<','<<v<<','<<s1.sum<<','<<s2.sum<<','<<s3.sum<<','<<lastF<<'\n';cp.flush();checkpoint*=10;}
  if(m%10000000==0)std::cout<<"m="<<m<<" minimum="<<std::setprecision(17)<<minv<<" at="<<minm<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
  // Insert n=m after evaluation: all running sums have strict n<m support.
  uint32_t base=0;if(ip<primes.size()&&primes[ip]==m){base=m;ip++;}if(ipp<powers.size()&&powers[ipp].n==m){if(base){std::cerr<<"duplicate atom";return 6;}base=powers[ipp].p;ipp++;}
  if(base){long double w=logl((long double)base)/sqrtl((long double)m);s1.add(w);s2.add(w*L);s3.add(w*L*L);}
 }
 if(!buf.empty()){raw.write((char*)buf.data(),buf.size()*sizeof(double));}
 raw.close();
 std::vector<std::pair<long double,uint32_t>>best;while(!top.empty()){best.push_back(top.top());top.pop();}std::sort(best.begin(),best.end());std::ofstream twenty(out+"/TWENTY_SMALLEST_NATIVE.csv");twenty<<"rank,m,log_m,Psi\n"<<std::setprecision(23);for(size_t i=0;i<best.size();i++)twenty<<i+1<<','<<best[i].second<<','<<logl((long double)best[i].second)<<','<<best[i].first<<'\n';
 std::ofstream plot(out+"/LOG_ENVELOPE.csv");plot<<"bin,m_first,m_last,m_min,m_max,Psi_min,Psi_max\n"<<std::setprecision(23);for(int i=0;i<NB;i++){auto b=bins[i];if(b.lo)plot<<i<<','<<b.lo<<','<<b.hi<<','<<b.minm<<','<<b.maxm<<','<<b.low<<','<<b.high<<'\n';}
 std::ofstream summary(out+"/NATIVE_SUMMARY.json");summary<<std::setprecision(23)<<"{\n\"max_m\":"<<M<<",\n\"evaluated_integers\":"<<(M-1)<<",\n\"long_double_mantissa_bits\":"<<std::numeric_limits<long double>::digits<<",\n\"prime_count\":"<<primes.size()<<",\n\"higher_prime_power_count\":"<<powers.size()<<",\n\"minimum\":\""<<minv<<"\",\n\"minimum_m\":"<<minm<<",\n\"maximum\":\""<<maxv<<"\",\n\"maximum_m\":"<<maxm<<",\n\"minimum_ge_1000\":\""<<min1000<<"\",\n\"minimum_ge_1000_m\":"<<min1000m<<",\n\"nonpositive_count\":"<<nonpositive<<",\n\"record_count\":"<<records<<",\n\"mean_uniform_m\":\""<<mean.sum/(M-1)<<"\",\n\"mean_uniform_t_continuous\":\""<<(lastF-F2)/(LM-L0)<<"\",\n\"mean_uniform_t_trapezoid\":\""<<trap.sum/(LM-L0)<<"\",\n\"mean_uniform_t_from_zero\":\""<<(lastF-FZERO)/LM<<"\",\n\"primitive_at_log2\":\""<<F2<<"\",\n\"primitive_at_log_max\":\""<<lastF<<"\",\n\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n}\n";
}
