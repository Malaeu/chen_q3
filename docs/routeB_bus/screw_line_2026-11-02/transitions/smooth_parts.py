"""Fixed-N, fixed-active-head smooth derivatives and separate atomic kicks.

The left continuation excludes the birth integer m on BOTH sides of the
central difference. Right derivative is left plus the rank-one kick.
"""
from pathlib import Path
import sys,csv,json,time,hashlib,argparse,os
from flint import arb,acb,arb_mat,ctx
P=Path(__file__).resolve().parent;ROOT=P.parent
sys.path.insert(0,str(ROOT/'kernels'))
import screw_kernels as sk
from local_source import source_matrix_local
def e_matrix(nodes,m,L):
 rows=[];pi=arb.pi();sq=arb(2).sqrt()
 for g,delta,kind in nodes:
  z=acb(arb(g),arb(delta));vv=[]
  for n in range(m+1):
   ds=arb(1) if n==0 else sq;w=2*pi*n/L;v=2*ds*z*(z*L/2).sin()/(L.sqrt()*(z*z-w*w))
   vv.append(sk.mid(sq*(v.real if kind=='real' else v.imag)) if kind!='line' else sk.mid(v.real))
  rows.append(vv)
 return arb_mat(rows)
def columns(m,L):
 names=[];cols=[];pi=arb.pi();sq=arb(2).sqrt()
 for gauge in ['physical','fourier']:
  for et in ['0.5','1','2']:
   eta=arb(et);c=[]
   for n in range(m+1):
    ds=arb(1) if n==0 else sq;w=2*pi*n/L
    v=ds*(-1)**n*(w*eta).cosh()/L.sqrt() if gauge=='physical' else 2*ds*eta*(eta*L/2).sinh()/(L.sqrt()*(eta*eta+w*w))
    c.append(sk.mid(v))
   cols.append(c);names.append((gauge,et))
 return arb_mat([[c[i] for c in cols] for i in range(m+1)]),names
def case(m,world,inp,bits=1024,htext='1e-30'):
 ctx.prec=bits;start=time.monotonic();L=arb(m).log();T=arb('1.1')*2*arb.pi()*m/L;h=arb(htext)
 zeta=[r['gamma'] for r in csv.DictReader((inp/'zeta_zeros_capacity.csv').open())];dh=json.loads((inp/'edge_law/dh/dh_zeros_extended.json').read_text());nodes=[];allg=[]
 if world=='zeta':
  for g in zeta:
   allg.append(arb(g))
   if arb(g)<T:nodes.append((g,'0','line'))
 else:
  for r in dh['critical_line_zeros']:
   allg.append(arb(r['gamma']))
   if arb(r['gamma'])<T:nodes.append((r['gamma'],'0','line'))
  for r in dh['off_line_pairs']:
   allg.append(arb(r['gamma']))
   if arb(r['gamma'])<T:
    de=sk.text(arb(r['sigma_right'])-arb('0.5'),90)
    nodes.extend([(r['gamma'],de,'real'),(r['gamma'],de,'imag')])
 b=sk.coefficients(m,world);Ks={};cross=None;names=None;baseK=None;eq=None
 for sign in [-1,0,1]:
  ell=L*(h*sign).exp();A,meta=source_matrix_local(m,world,b,ell);E=e_matrix(nodes,m,ell);C,names=columns(m,ell);B=(E*A*E.transpose()).mid();V=(E*C).mid();X=B.solve(V,algorithm='approx');K=(V.transpose()*X).mid();Ks[sign]=[K[j,j] for j in range(K.nrows())]
  if sign==0:
   eb=arb_mat([[sk.mid((arb(1) if n==0 else arb(2).sqrt())/ell.sqrt())] for n in range(m+1)])
   cr=(eb.transpose()*E.transpose()*X).mid();cross=[cr[0,j] for j in range(cr.ncols())];baseK=Ks[0]
 rows=[];wn=b[m]/arb(m).sqrt()
 for j,(gauge,et) in enumerate(names):
  eta=arb(et);K=baseK[j];dk=(Ks[1][j]-Ks[-1][j])/(2*h);kick=2*wn*L*cross[j]*cross[j]
  defined=K!=0 and Ks[-1][j]!=0 and Ks[1][j]!=0
  dr=(1/(eta*Ks[1][j])-1/(eta*Ks[-1][j]))/(2*h) if defined else None
  dr_chain=-dk/(eta*K*K) if defined else None;jr=-kick/(eta*K*K) if defined else None
  rows.append(dict(world=world,m=m,q=len(nodes),gauge=gauge,eta=et,K=sk.text(K),endpoint_cross=sk.text(cross[j]),
   arithmetic_weight_b_over_sqrt_n=sk.text(wn),smooth_left_dotK_tau=sk.text(dk),atomic_jump_dotK_tau=sk.text(kick),right_dotK_tau=sk.text(dk+kick),
   smooth_left_dotr_proxy_tau=sk.text(dr) if dr is not None else 'undefined',atomic_jump_dotr_proxy_tau=sk.text(jr) if jr is not None else 'undefined',
   right_dotr_proxy_tau=sk.text(dr+jr) if dr is not None else 'undefined',radius_chain_rule_fd_error=sk.text(abs(dr-dr_chain)) if dr is not None else 'undefined',
   FD_h=htext,arithmetic_bits=bits,source_path='fixed integer N=m; L_tau=L exp(tau); same actual zero nodes; birth integer m excluded in smooth continuation',
   actual_Weyl_status='NOT_IDENTIFIED; formal_inverse_form_only'))
 rec=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,m=m,q=len(nodes),bits=bits,h=htext,
  cutoff_nearest_margin=sk.text(min(abs(g-T) for g in allg)),same_active_zero_set=True,birth_integer_excluded_in_both_fd_sides=True,
  original_source_sha256=hashlib.sha256((ROOT/'kernels/screw_kernels.py').read_bytes()).hexdigest(),local_source_sha256=hashlib.sha256((P/'local_source.py').read_bytes()).hexdigest(),
  numerical_second_order_error_not_interval_enclosed=True,rows=rows,seconds=time.monotonic()-start)
 dest=P/f'smooth_{world}_m{m}_bits{bits}_h{htext}.json';dest.write_text(json.dumps(rec,indent=2)+'\n');print(world,m,'smoothparts',rec['seconds'],flush=True)
 return rec
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--input-root',type=Path,required=True);a.add_argument('--m',type=int,nargs='+',required=True);a.add_argument('--world',nargs='+',choices=['zeta','dh'],default=['zeta','dh']);a.add_argument('--bits',type=int,default=1024);a.add_argument('--h',default='1e-30');q=a.parse_args()
 for m in q.m:
  for world in q.world:case(m,world,q.input_root,q.bits,q.h)
