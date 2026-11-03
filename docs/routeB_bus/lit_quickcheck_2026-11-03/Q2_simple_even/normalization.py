from check import *
sys.path.insert(0,str(P.parents[1]/'screw_line_2026-11-02/innovation_law/core'))
from scan import source

def main():
 mp.mp.dps=80;rows=[]
 for m in [3,7,20,47]:
  L=mp.log(m);omega=2*mp.pi/L
  for world in ['zeta','dh','plant']:
   E,O=build(m,1,'dh' if world=='dh' else 'zeta',80)
   if world=='plant':E,O=plant(E,O,L)
   g,_=source(world,mp.mpf(6));constant=-2*g(L)/L
   c=-mp.euler-mp.log(8*mp.pi/(5 if world=='dh' else 1))+(1 if world=='dh' else -1)*mp.pi/2
   alpha=mp.mpf('1.5') if world=='dh' else mp.mpf('.5');z=mp.exp(-L/2);tail=mp.atanh(z)+(mp.atan(z) if world!='dh' else -mp.atan(z))
   def corr(s):return (1-s/L)*mp.cos(omega*s)+mp.sin(omega*s)/(omega*L)
   arch=2*mp.quad(lambda s:mp.exp(-alpha*s)/(-mp.expm1(-2*s))*(1-corr(s)),[0,L/4,L/2,L])+2*tail
   bb=coeffs(m,'dh' if world=='dh' else 'zeta');arith=-2*mp.fsum(bb[n]/mp.sqrt(n)*corr(mp.log(n)) for n in range(2,m))
   f=lambda x:mp.sqrt(2/L)*mp.sin(omega*x)
   Aplus=mp.quad(lambda x:f(x)*mp.exp(x/2),[-L/2,0,L/2]);Aminus=mp.quad(lambda x:f(x)*mp.exp(-x/2),[-L/2,0,L/2]);pole=2*Aplus*Aminus if world!='dh' else mp.mpf(0)
   extra=0
   if world=='plant':
    w=2*mp.pi/mp.log(2)+mp.j/4;S=mp.quad(lambda x:f(x)*mp.sin(w*x),[-L/2,0,L/2]);extra=4*mp.re(S*S)
   direct=c+arch+arith+pole+extra
   rows.append(dict(world=world,m=m,constant_entry_matrix=mp.nstr(E[0,0],70),constant_entry_g=mp.nstr(constant,70),constant_difference=mp.nstr(abs(E[0,0]-constant),25),odd_entry_matrix=mp.nstr(O[0,0],70),odd_entry_physical=mp.nstr(direct,70),odd_difference=mp.nstr(abs(O[0,0]-direct),25)))
 with (P/'normalization_controls.csv').open('w',newline='') as f:
  wr=csv.DictWriter(f,fieldnames=rows[0]);wr.writeheader();wr.writerows(rows)
 print('maximum difference',mp.nstr(max(mp.mpf(r[k]) for r in rows for k in ['constant_difference','odd_difference']),20),flush=True)
if __name__=='__main__':main()
