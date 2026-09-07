"""Final numbers for THREE_LOBE_PREFLIGHT_REPORT."""
import sys, time
import mpmath as mp
from flint import arb, ctx
sys.path.insert(0,'/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/three_lobe')
from tl_cache import get
from tl_kernel import kernel_basis
from tl_analyze import to_mp, congr, gen_eig
import tl_certify as CT

t0=time.time(); mp.mp.dps=50
base = get(dps=50)
P = base['P']; K = to_mp(kernel_basis())
M7 = {nm: congr(K, base[nm]) for nm in ('G','Q','Arch','Prime','Pole','D')}
G7, Q7 = M7['G'], M7['Q']
# G-unit rescaling of the kernel basis (generalized eigenvalues invariant)
s = [1/mp.sqrt(G7[a,a]) for a in range(7)]
def rs(M): return mp.matrix([[M[a,b]*s[a]*s[b] for b in range(7)] for a in range(7)])
Gt, Qt = rs(G7), rs(Q7)
E, V, L = gen_eig(Q7, G7)
print('== packet =='); print('delta   =', mp.nstr(P['delta'],25))
print('c_A     =', mp.nstr(P['cA'],25)); print('m_eta   =', mp.nstr(base['m_eta'],25))
print('w2,w3   =', mp.nstr(P['L2']/mp.sqrt(2),20), mp.nstr(P['L3']/mp.sqrt(3),20))
print('supp diam log3+delta =', mp.nstr(P['L3']+P['delta'],15), ' log4 =', mp.nstr(mp.log(4),15))
print('active n:', [(n, mp.nstr(w,15)) for n,w in base['active']])
print('\n== 3x3 profile Gram g ==')
for j in range(3): print('  ', '  '.join(mp.nstr(base['g'][j,k],17) for k in range(3)))
print('\n== G7 (kernel basis rescaled to unit G-norm) ==')
for a in range(7): print('  ', '  '.join('%9.6f'%float(Gt[a,b]) for b in range(7)))
print('\n== Q7 (same basis) ==')
for a in range(7): print('  ', '  '.join('%10.6f'%float(Qt[a,b]) for b in range(7)))
print('\n== Q7 raw diagonal / G7 raw diagonal ==')
for a in range(7): print('   B%d  G=%s  Q=%s' % (a+1, mp.nstr(G7[a,a],14), mp.nstr(Q7[a,a],14)))
print('\n== generalized eigenvalues lam(Q7,G7) ==')
for x in E: print('  ', mp.nstr(x,22))
v = V[0]; nv = mp.sqrt((v.T*G7*v)[0]); v = v/nv
print('minimiser (G-unit, kernel coords B1..B7):')
print('  ', '  '.join('%+.6f'%float(v[a]*mp.sqrt(G7[a,a])) for a in range(7)))
print('  Rayleigh check:', mp.nstr((v.T*Q7*v)[0]/(v.T*G7*v)[0], 22))
sp_ = {}
for nm in ('Q','Arch','Prime','Pole','D'):
    sp_[nm] = (v.T*M7[nm]*v)[0]/(v.T*G7*v)[0]
print('  split at minimiser: ' + '  '.join('%s=%s'%(k,mp.nstr(x,12)) for k,x in sp_.items()))
e1 = mp.matrix(7,1); e1[0]=1; n1=(e1.T*G7*e1)[0]
print('\n== mean direction z (x) (1,0,0) ==')
print('  ||f_z||^2 = 12*g00 =', mp.nstr(n1,20))
for nm in ('Q','D','Arch','Prime','Pole'):
    print('  %-5s / ||f||^2 = %s' % (nm, mp.nstr((e1.T*M7[nm]*e1)[0]/n1, 22)))
print('  log(4/3)/6 =', mp.nstr(mp.log(mp.mpf(4)/3)/6,22))
print('  |Prime/||f||^2 - log(4/3)/6| =',
      mp.nstr(abs((e1.T*M7['Prime']*e1)[0]/n1 - mp.log(mp.mpf(4)/3)/6),4))
print('\n== unrestricted 9x9 (context) ==')
E9,_,_ = gen_eig(base['Q'], base['G'])
print('  lam(Q,G) 9x9:', '  '.join(mp.nstr(x,10) for x in E9))
pe = mp.eigsy(base['Pole'], eigvals_only=True)
print('  Pole eigenvalues (rank 2):', '  '.join(mp.nstr(x,10) for x in pe))
print('\n== archimedean cross entry at lag log(3/2) vs its prime atom ==')
Th = None
i1, i2 = 3*1+0, 3*2+0
print('  Arch[(log2,phi0),(log3,phi0)] =', mp.nstr(base['Arch'][i2,i1],17))
print('  Prime[(log2,phi0),(log3,phi0)] =', mp.nstr(base['Prime'][i2,i1],17), '(must be 0)')
print('  Prime[(0,phi0),(log2,phi0)] =', mp.nstr(base['Prime'][0,i1],17), ' -w2*g00 =',
      mp.nstr(-P['L2']/mp.sqrt(2)*base['g'][0,0],17))
print('  Prime[(0,phi0),(log3,phi0)] =', mp.nstr(base['Prime'][0,i2],17), ' -w3*g00 =',
      mp.nstr(-P['L3']/mp.sqrt(3)*base['g'][0,0],17))
print('\nelapsed %.1fs' % (time.time()-t0))
