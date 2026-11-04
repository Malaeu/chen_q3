#include <vector>
#include <fstream>
#include <cstdint>
#include <iostream>
int main(int argc,char**argv){const uint32_t N=100000000;std::vector<unsigned char>c(N/2+1,0);for(uint32_t p=3;(uint64_t)p*p<=N;p+=2)if(!c[p/2])for(uint64_t n=(uint64_t)p*p;n<=N;n+=2*p)c[n/2]=1;std::ofstream f(argv[1],std::ios::binary);uint32_t p=2;f.write((char*)&p,4);uint64_t count=1;for(p=3;p<=N;p+=2)if(!c[p/2]){f.write((char*)&p,4);++count;}std::cout<<"primes="<<count<<" through="<<N<<"\n";}
