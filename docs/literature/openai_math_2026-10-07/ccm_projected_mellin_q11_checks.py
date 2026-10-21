from fractions import Fraction as F
from math import prod
checks=0
for w in [F(1,3),F(1,7),F(2,5),F(1,11)]:
 c=[-F(3,8),2*(w*w+F(1,4)),-(4*w*w+F(1,4))/2]
 assert sum(c)==0;checks+=1
 norm=c[0]**2+(c[1]**2+c[2]**2)/2
 assert norm==F(35,128)+F(5,4)*w*w+4*w**4;checks+=1
 for a in [F(1,2),-F(1,2),F(1,4),F(1,3),F(1,5),F(2,5)]:
  lap=sum(c[j]*a/(a*a+j*j*w*w) for j in range(3))
  exact=(a*a-F(1,4))*6*w**4/(a*(a*a+w*w)*(a*a+4*w*w))
  assert lap==exact;checks+=1
  if abs(a)==F(1,2):assert lap==0;checks+=1
  else:assert lap!=0;checks+=1
print('PASS',checks,'rational formula controls; not a CCM or interval run')
