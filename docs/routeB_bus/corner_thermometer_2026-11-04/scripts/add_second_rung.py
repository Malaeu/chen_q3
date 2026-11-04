"""Row/diagonal analytic CCM source, all j, no full dense matrices; point diagnostics."""
import sys,importlib.util,csv,json,time,hashlib
from pathlib import Path
sys.path[:0]=['/workspace/second_moment/local/deps','/workspace/stiffness/deps']
import gmpy2 as g
from flint import arb,acb,ctx
OUT=Path('/workspace/corner_thermometer/output');SOURCE=Path('/workspace/stiffness/repo/docs/routeB_bus/ground_state_zeros_2026-11-03/inputs/analytic_source.py')
spec=importlib.util.spec_from_file_location('pinned_analytic',SOURCE);pinned=importlib.util.module_from_spec(spec);spec.loader.exec_module(pinned)
GRID=[16,40,80,160,300,1000,2000]
def calc(m,bits=256,worlds=('zeta','dh')):
 g.get_context().precision=bits;ctx.prec=bits+32;f=g.mpfr;L=g.log(m);pi=g.const_pi();z=g.exp(-L/2);sq2=g.sqrt(2);cut=g.exp2(-bits-20)
 def mid(v):return f(v.mid().str(int((bits+40)*.30103)+12,radius=False))
 coeff=pinned.coefficients(m,bits)
 g.get_context().precision=bits
 r=[g.log(n)/L for n in range(2,m)];co=[g.cos(2*pi*t)for t in r];si=[g.sin(2*pi*t)for t in r];cs=[f(1)]*len(r);sn=[f(0)]*len(r)
 pars={}
 for w in worlds:
  k=int(w=='dh');alpha=f('1.5')if k else f('.5');terms=[];a=alpha
  while g.exp(-a*L)>cut:terms.append((a,g.exp(-a*L)));a+=2
  zz=acb(arb(str(alpha/2)));p0=mid(zz.digamma().real);t0=mid(zz.polygamma(1).real)
  c=-g.const_euler()-g.log(8*pi/(5 if k else 1))+(pi/2 if k else-pi/2)
  tail=g.atanh(z)+(-g.atan(z)if k else g.atan(z))
  pars[w]=(k,terms,p0,t0,c,tail,[coeff[k][n]/g.sqrt(n)for n in range(2,m)])
 rows=[];a00={}
 for j in range(m+1):
  om=2*pi*j/L;om2=om*om
  for w in worlds:
   k,terms,p0,t0,c,tail,weights=pars[w]
   ps=sum((ww*s for ww,s in zip(weights,sn)),f(0))
   pd=sum((ww*(2*(1-t)*cc-(ss/(pi*j)if j else f(0)))for ww,t,cc,ss in zip(weights,r,cs,sn)),f(0))
   if j:
    zz=acb(arb(str((f('1.5')if k else f('.5'))/2)),arb(str(om/2)));psi=zz.digamma();tri=zz.polygamma(1)
    re,im,rt=mid(psi.real),mid(psi.imag),mid(tri.real)
    moment=im/2-sum((om*e/(a*a+om2)for a,e in terms),f(0))
    dg=re-p0+rt/(2*L)+im/(L*om)-sum((e*(2*om2/(a*(a*a+om2))+4*a*a/(L*(a*a+om2)**2)+2*a/(a*a+om2))for a,e in terms),f(0))
   else:
    dg=t0/(2*L)-2/L*sum((e/(a*a)for a,e in terms),f(0))-2*sum((e/a for a,e in terms),f(0));moment=f(0)
   diagonal=c+dg+2*tail-pd
   pole0=4*sq2*L**f('1.5')*g.sinh(L/4)/(L*L)
   polej=4*sq2*(sq2 if j else 1)*L**f('1.5')*g.sinh(L/4)/(L*L+16*pi*pi*j*j)
   if not k:diagonal+=polej*polej
   if j==0:a00[w]=diagonal;continue
   row=sq2*(moment+ps)/(pi*j)
   if not k:row+=pole0*polej
   det=a00[w]*diagonal-row*row;den=a00[w]*diagonal
   ratio=row*row/den if den else None
   def dec(v):return None if v is None else format(v,'.68g')
   rows.append(dict(world=w,m=m,j=j,omega=dec(om),A00=dec(a00[w]),A0j=dec(row),Ajj=dec(diagonal),determinant=dec(det),raw_ratio=dec(ratio),denominator_positive=bool(den>0),A00_positive=bool(a00[w]>0),Ajj_positive=bool(diagonal>0),PSD_minor_pass=bool(a00[w]>=0 and diagonal>=0 and det>=0),bits=bits))
  cs,sn=([cc*u-ss*v for cc,ss,u,v in zip(cs,sn,co,si)],[ss*u+cc*v for cc,ss,u,v in zip(cs,sn,co,si)])
 return rows

def main():
 start=time.monotonic();allrows=[];summary=[]
 for m in GRID:
  rows=calc(m);allrows+=rows
  for w in ['zeta','dh']:
   rr=[r for r in rows if r['world']==w];pos=[r for r in rr if r['denominator_positive']];maximum=max(pos,key=lambda r:g.mpfr(r['raw_ratio']))if pos else None;minimum=min(rr,key=lambda r:g.mpfr(r['determinant']))
   summary.append(dict(world=w,m=m,max_positive_denominator_ratio=maximum,min_determinant=minimum,failed_minors=sum(not r['PSD_minor_pass']for r in rr),nonpositive_denominators=sum(not r['denominator_positive']for r in rr)))
  print('GRID',m,'seconds',time.monotonic()-start,flush=True)
 first=None;scan=[]
 for m in range(2,2001):
  rr=calc(m,worlds=('dh',));bad=[r for r in rr if not r['PSD_minor_pass']];scan.append(dict(m=m,min_determinant=min((r['determinant']for r in rr),key=g.mpfr),failed_minors=len(bad)))
  if bad:first=dict(m=m,failed_rows=bad,all_rows=rr);break
 critical=[r for r in allrows if (r['world']=='zeta' and r['raw_ratio']is not None and g.mpfr(r['raw_ratio'])>g.mpfr('0.999999')) or (r['world']=='dh' and not r['PSD_minor_pass'])]
 confirmation=[]
 for m in sorted(set([r['m']for r in critical]+([first['m']]if first else[]))):
  rr=calc(m,320);wanted={(r['world'],r['j'])for r in critical if r['m']==m}
  if first and m==first['m']:wanted|={(r['world'],r['j'])for r in first['failed_rows']}
  confirmation +=[r for r in rr if(r['world'],r['j'])in wanted]
 with(OUT/'ADD_SECOND_RUNG.csv').open('w')as h:
  wr=csv.DictWriter(h,fieldnames=list(allrows[0]));wr.writeheader();wr.writerows(allrows)
 result=dict(status='DIAGNOSTIC_POINT_SOURCE_NOT_INTERVAL',registration='bb91ed2018ff4b92f7cfc4fe60b6b0bf2ff76a73',source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),grid=GRID,bits=256,confirmation_bits=320,summary=summary,DH_exhaustive_integer_scan=scan,DH_first_failure=first,zeta_near_one_threshold='0.999999',critical_confirmation=confirmation,seconds=time.monotonic()-start,full_matrices_built=False,negative_denominator_ratios_are_not_PSD_criteria=True)
 (OUT/'ADD_SECOND_RUNG.json').write_text(json.dumps(result,indent=2)+'\n');print('DONE',result['seconds'],'first',None if first is None else first['m'],'critical',len(critical),flush=True)
if __name__=='__main__':main()
