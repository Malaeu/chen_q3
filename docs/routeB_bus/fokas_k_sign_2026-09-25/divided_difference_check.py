"""Exact rational controls for the two-energy recurrence; no spectral claim."""
from fractions import Fraction as Q

def seq(G,e,N):
    out=[Q(0),Q(1)]
    for k in range(N):
        lo=-G*Q((2*k-1)*2*k,(4*k-3)*(4*k-1))
        up=-G*Q((2*k+1)*(2*k+2),(4*k+3)*(4*k+5))
        d=2*k*(2*k+1)+G*Q(4*k*(2*k+1)-1,(4*k-1)*(4*k+3))
        out.append(((e-d)*out[-1]-lo*out[-2])/up)
    return out
count=0
for G in (Q(1),Q(7,3),Q(100)):
 for e0,e4 in ((Q(2),Q(3)),(Q(-2,3),Q(7,5)),(Q(0),Q(11))):
    a,b=seq(G,e0,18),seq(G,e4,18);s=[Q(0),Q(0)]
    for k in range(18):
        lo=-G*Q((2*k-1)*2*k,(4*k-3)*(4*k-1))
        up=-G*Q((2*k+1)*(2*k+2),(4*k+3)*(4*k+5))
        d=2*k*(2*k+1)+G*Q(4*k*(2*k+1)-1,(4*k-1)*(4*k+3))
        s.append((b[k+1]+(e0-d)*s[-1]-lo*s[-2])/up)
        assert (a[k+2]-b[k+2])==(e0-e4)*s[-1]
        count+=1
print(f'{count} exact Fraction recurrence identities passed; polynomial identity follows by induction.')
