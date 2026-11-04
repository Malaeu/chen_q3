"""Every integer DH row0/diag screen through2000; selected highprecision returns."""
import importlib.util,json,csv,time
from pathlib import Path
P=Path('/workspace/corner_thermometer/output/scripts/add_second_rung_raw.py');spec=importlib.util.spec_from_file_location('rawengine',P);raw=importlib.util.module_from_spec(spec);spec.loader.exec_module(raw)
np=raw.np;g=raw.exact.g;acb=raw.exact.acb;arb=raw.exact.arb;ctx=raw.exact.ctx;OUT=raw.OUT

def selected(m,js,bits=256):
 g.get_context().precision=bits;ctx.prec=bits+32;f=g.mpfr;L=g.log(m);pi=g.const_pi();sq2=g.sqrt(2);co=raw.exact.pinned.coefficients(2000,256)[1];g.get_context().precision=bits
 def mid(v):return f(v.mid().str(95,radius=False))
 terms=[];a=f('1.5');cut=g.exp2(-bits-20)
 while g.exp(-a*L)>cut:terms.append((a,g.exp(-a*L)));a+=2
 z=acb(arb('.75'));p0=mid(z.digamma().real);t0=mid(z.polygamma(1).real);c=-g.const_euler()-g.log(8*pi/5)+pi/2;zz=g.exp(-L/2);tail=g.atanh(zz)-g.atan(zz)
 rr=[g.log(n)/L for n in range(2,m)];weights=[co[n]/g.sqrt(n)for n in range(2,m)]
 a00=c+t0/(2*L)-2/L*sum((e/(a*a)for a,e in terms),f(0))-2*sum((e/a for a,e in terms),f(0))+2*tail-2*sum((w*(1-r)for w,r in zip(weights,rr)),f(0))
 out=[]
 for j in js:
  om=2*pi*j/L;om2=om*om;z=acb(arb('.75'),arb(str(om/2)));psi=z.digamma();tri=z.polygamma(1);re,im,rt=mid(psi.real),mid(psi.imag),mid(tri.real)
  sums=f(0);pd=f(0)
  for w,r in zip(weights,rr):
   angle=2*pi*j*r;sn=g.sin(angle);cs=g.cos(angle);sums+=w*sn;pd+=w*(2*(1-r)*cs-sn/(pi*j))
  moment=im/2-sum((om*e/(a*a+om2)for a,e in terms),f(0))
  dg=re-p0+rt/(2*L)+im/(L*om)-sum((e*(2*om2/(a*(a*a+om2))+4*a*a/(L*(a*a+om2)**2)+2*a/(a*a+om2))for a,e in terms),f(0))
  ajj=c+dg+2*tail-pd;row=sq2*(moment+sums)/(pi*j);det=a00*ajj-row*row;ratio=row*row/(a00*ajj)
  out.append(dict(m=m,j=j,bits=bits,omega=format(om,'.68g'),A00=format(a00,'.68g'),A0j=format(row,'.68g'),Ajj=format(ajj,'.68g'),determinant=format(det,'.68g'),raw_ratio=format(ratio,'.68g'),denominator_positive=bool(a00*ajj>0),PSD_minor_pass=bool(a00>=0 and ajj>=0 and det>=0)))
 return out

def main():
 start=time.monotonic();rows=[];targets={};firstRaw=None;firstPSD=None
 for m in range(2,2001):
  r,rat,det,dg=raw.calc(m);r.update(min_Ajj=float(min(dg[1:])),negative_Ajj_count=int(np.sum(dg[1:]<0)),negative_det_count=int(np.sum(det<0)),raw_above_one_count=int(np.sum(rat>1)),raw_above_guard_count=int(np.sum(rat>.999999)))
  if firstRaw is None and r['max_rawratio']>1:firstRaw=dict(m=m,j=r['argj'],raw_ratio=r['max_rawratio'])
  if firstPSD is None and(r['A00']<0 or r['min_Ajj']<0 or r['min_det']<0):firstPSD=dict(m=m,j=r['argmin_det'],min_det=r['min_det'])
  js=[int(j)for j in np.where(rat>.999999)[0]+1]
  if m>=464 and js:targets[m]=js
  rows.append(r)
  if m%100==0:print('DENSE',m,'seconds',time.monotonic()-start,'targetrows',sum(map(len,targets.values())),flush=True)
 with(OUT/'ADD_DH_DENSE.csv').open('w')as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
 confirmations=[]
 for m,js in targets.items():
  confirmations+=selected(m,js)
  if m%100==0:print('CONFIRM',m,time.monotonic()-start,flush=True)
 # Selected-cell engine checks against full row/diagonal highprecision implementation.
 engine=[]
 for m,js in [(75,[58]),(463,[234]),(2000,[1,290])]:
  full={r['j']:r for r in raw.exact.calc(m,256,worlds=('dh',))};test=selected(m,js)
  for r in test:
   delta=max(abs(g.mpfr(r[k])-g.mpfr(full[r['j']][k]))for k in ['A00','A0j','Ajj','raw_ratio','determinant']);engine.append(dict(m=m,j=r['j'],max_printed_difference=format(delta,'.10g'),pass_gate=bool(delta<g.mpfr('1e-60'))))
 out=dict(status='DIAGNOSTIC_FLOAT64_ALL_INTEGER_SCREEN_WITH_256BIT_SELECTED_CONFIRMATIONS',scope='all integer m2..2000, everyj1..m, DH row0anddiagonal only',first_raw_crossing_screen=firstRaw,first_PSD_failure_screen=firstPSD,new_confirmation_scope='all screen rawratio>.999999 on integer m464..2000',selected_confirmation_bits=256,new_target_m_count=len(targets),new_target_row_count=len(confirmations),new_selected_confirmations=confirmations,selected_engine_validation=engine,all_selected_engine_gates_pass=all(r['pass_gate']for r in engine),seconds=time.monotonic()-start,full_matrices_built=False,interval_certificate=False,frozen_first_RAW_files_unchanged=True)
 (OUT/'ADD_DH_DENSE.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',out['seconds'],out['new_target_row_count'],flush=True)
if __name__=='__main__':main()
