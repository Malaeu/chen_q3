import sys; sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import numpy as np, dens
a=np.log(2.0); r=2**-0.5
T=np.load('t_tables.npz'); xi=T['xi']
Di=np.load('d_inf.npz'); dinf=Di['d']; qinf=Di['q']
g2=dens.gamma_S(xi,(2,)); q2=dens.q_S(xi,(2,))
res={}
for J in [6,7,8]:
    try: O=np.load(f'op_two_J{J}.npz')
    except Exception: continue
    d=2*np.real(g2*(T['t_2']+O['mix']))-2*O['quad']
    res[J]=dict(d=d,quad=O['quad'],mix=O['mix'],un2=O['unorm2'],lam=O['lam'],
                ndrop=int(O['ndrop']),lead=2*np.real(g2*T['t_2']))
np.savez('d_two.npz', xi=xi, **{f'd_J{J}':res[J]['d'] for J in res},
         **{f'un2_J{J}':res[J]['un2'] for J in res}, lead=res[max(res)]['lead'],
         q2=q2, dinf=dinf, qinf=qinf)

def show():
    Js=sorted(res)
    print("xi      "+"".join(f"  d_2 (J={J})   " for J in Js)+"  2Re(g t_2)     -2||u||^2   d_inf")
    for x in [0,2,5,10,16,20,30,40,60,80,120,200,300,400,600]:
        i=int(round(x/0.25))
        print(f"{x:6.1f} "+"".join(f"{res[J]['d'][i]:+14.6e}" for J in Js)+
              f"{res[Js[-1]]['lead'][i]:+14.6e}{-2*res[Js[-1]]['un2'][i]:+13.4e}{dinf[i]:+12.4e}")
    print("\n  J-spread (operator truncation) |d_2^(J)-d_2^(J-1)|:")
    for lo,hi in [(0,16),(16,60),(60,120),(120,300),(300,600)]:
        m=(xi>=lo)&(xi<=hi)
        line=f"  [{lo},{hi}] "
        for k in range(1,len(Js)):
            dd=res[Js[k]]['d'][m]-res[Js[k-1]]['d'][m]
            line+=f" J{Js[k]}-J{Js[k-1]}: max={np.abs(dd).max():.2e} rms={np.sqrt((dd**2).mean()):.2e} "
        rel=np.abs(res[Js[-1]]['d'][m]); line+=f" |max d_2|={rel.max():.2e}"
        print(line)
if __name__=='__main__':
    show()
