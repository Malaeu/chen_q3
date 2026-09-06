"""S5: m(h) = - int W_h d_2 dxi,  W_h = (1-cos a xi)|hhat|^2 / H  (verdict (21))."""
import sys; sys.path.insert(0,'/home/chirurgie/.claude/jobs/4b35770d/tmp/mellin_d2')
import numpy as np
a=np.log(2.0); H=1.6434228127646e8
C=np.load('/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/docs/routeB_bus/phase5_codex/density_fine_N4096.npy')
D=np.load('d_two.npz'); xi=D['xi']
assert np.abs(C[0]-xi).max()==0
W=(1-np.cos(a*xi))*C[4]/H            # even in xi
mass=2*np.trapz(W,xi); tailmass=2*np.pi-mass
def I(f):  return 2*np.trapz(W*f,xi)   # full-line integral against W_h
out={}
for k in ['d_J6','d_J7','d_J8']:
    if k in D: out[k]=-I(D[k])
out['lead_only']=-I(D['lead'])
out['d_inf']=I(D['dinf'])            # A(h) = -int W d_inf ; report int W d_inf too
print(f"int_full W_h (grid, |xi|<=600) = {mass:.6f}   Lemma 5 exact 2pi = {2*np.pi:.6f}"
      f"   missing tail mass = {tailmass:.6f} ({100*tailmass/(2*np.pi):.2f}%)")
print()
for k,v in out.items(): print(f"  {k:12s}: -int W_h d = {v:+.6f}" if k!='d_inf' else f"  int W_h d_inf = {v:+.6f}")
if 'd_J8' in D:
    print(f"\n  A(h) = -int W_h d_inf              = {-out['d_inf']:+.6f}")
    print(f"  int W_h (d_2 - d_inf)  (J=8)       = {I(D['d_J8']-D['dinf']):+.6f}")
    print(f"  w = a/sqrt(2)                      = {a/np.sqrt(2):+.6f}")
    print(f"  B(h) = w + int W_h(d_2-d_inf)      = {a/np.sqrt(2)+I(D['d_J8']-D['dinf']):+.6f}")
    sup=np.abs(D['d_J8'][xi>=550]).max()
    print(f"\n  |d_2| on [550,600] <= {sup:.4e};  |tail beyond 600| <= {tailmass*sup:.4e}")
