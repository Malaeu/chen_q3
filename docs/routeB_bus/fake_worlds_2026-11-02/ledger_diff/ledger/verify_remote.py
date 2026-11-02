"""Independent evaluation of six already-published native trial vectors.
No new eigensystem. DIAGNOSTIC_NEVER_A_PROOF.
"""
from pathlib import Path
import json,sys,time,hashlib,os
import mpmath as mp
import ledger
P=Path(__file__).resolve().parent
R=Path(os.environ.get('REMOTE_LEDGER',str(P.parent/'ledger_cells')))

def run(name):
 start=time.monotonic();mp.mp.dps=120
 p=R/name;src=json.loads(p.read_text());s=src['summary'];m=int(s['m']);world='DH' if s['world']=='dh' else 'zeta'
 v=mp.matrix(src['unit_physical_modal_vector']);v/=mp.norm(v)
 A,H,pole,c,b=ledger.build(m,world);D,S=ledger.qcoeff(v,m);L=mp.log(m)
 groups={'H_original':(v.T*H*v)[0],'constant_original':c,'pole':(v.T*pole*v)[0]}
 arith={}
 for sector in ('prime','square','higherpower','nonprimepower'):
  for sign in ('b_positive','b_negative'):arith[sector+'_'+sign]=mp.mpf(0)
 for n in range(2,m+1):
  if not b[n]:continue
  pp=ledger.prime_power(n);sector='nonprimepower' if not pp else ('prime' if pp[1]==1 else 'square' if pp[1]==2 else 'higherpower')
  sign='b_positive' if b[n]>0 else 'b_negative'
  arith[sector+'_'+sign]+=-b[n]/mp.sqrt(n)*ledger.qvalue(mp.log(n),D,S,L)
 differences={k:groups[k]-mp.mpf(s[k]) for k in groups}
 for k,value in arith.items():differences['signed_minus_P_'+k]=value-mp.mpf(s['signed_minus_P_'+k])
 direct=mp.fsum(groups.values())+mp.fsum(arith.values());ray=(v.T*A*v)[0]
 ref=ledger.abel_ledger(v,m,b,reference=True)
 for key,remote in [('boundary_B','reference_B'),('interior_I','reference_derivative_bulk'),('half_Q','reference_T'),('continuum','continuum_I_L')]:differences[key]=ref[key]-mp.mpf(s[remote])
 raw=ledger.abel_ledger(v,m,b,reference=(world=='zeta'))
 for key,remote in [('boundary_B','boundary_B'),('interior_I','derivative_bulk'),('half_Q','half_correlation_T')]:differences['canonical_'+key]=raw[key]-mp.mpf(s[remote])
 checks=dict(remote_same_vector_Rayleigh_difference=ray-mp.mpf(s['same_vector_Rayleigh']),independent_direct_sum_minus_rayleigh=direct-ray,reference_Abel_identity=ref['abel_identity_residual'],canonical_Abel_identity=raw['abel_identity_residual'],max_component_difference=max(abs(x) for x in differences.values()))
 if world=='zeta':
  hp=groups['H_original']-4+ref['decaying_continuum'];checks['H_plus_difference']=hp-mp.mpf(s['H_plus']);checks['pole_continuum_identity']=groups['pole']-ref['continuum']-ref['decaying_continuum'];checks['transformed_rayleigh_difference']=hp+4+c-ref['abel_sum']-ray
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',remote_commit='8acecc1574740c5163c2a4e8ef75049f6df84313',remote_file=name,world=world,m=m,dps=120,order=128,new_eigensystem=False,vector_norm=mp.norm(v),rayleigh=ray,groups=groups,arithmetic_signed_groups=arith,reference_Abel=ref,canonical_Abel=raw,differences=differences,checks=checks,seconds=time.monotonic()-start)
 (P/('verification_'+name)).write_text(json.dumps(ledger.fmt(out),indent=2)+'\n');print(name,{k:mp.nstr(x,8) for k,x in checks.items()},'seconds',time.monotonic()-start,flush=True)

if __name__=='__main__':run(sys.argv[1])
