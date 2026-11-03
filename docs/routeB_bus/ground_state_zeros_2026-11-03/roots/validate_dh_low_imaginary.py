from pathlib import Path
import sys,json,resource,time,os,hashlib
resource.setrlimit(resource.RLIMIT_CPU,(2,2));sys.path.insert(0,'/workspace/conditioning_deps')
import mpmath as mp
from flint import arb,ctx
P=Path(__file__).resolve().parent;mp.mp.dps=220;ctx.prec=2000;m=300
res=json.loads((P/'results/dh_even_m300.json').read_text());source=Path(res['source_vector_path']);source=source if source.exists() else P.parent/'spectra/vectors'/source.name;source_blob=source.read_bytes();assert hashlib.sha256(source_blob).hexdigest()==res['source_vector_sha256'];d=json.loads(source_blob);c=list(map(mp.mpf,d['v_even0_low']));a=[mp.mpf(n*n)/(m*m) for n in range(1,m+1)];Omhi=mp.mpf(res['Omega']);Omlo=2*mp.pi*m/mp.mpf(d['L_low']);seed=next(r for r in res['roots'] if r['kind']=='polynomial_pure_imaginary');uhi=mp.mpf(seed['u_re']);u=uhi
for it in range(10):
 r=c[0]+mp.sqrt(2)*mp.fsum(cn*u/(u-an) for cn,an in zip(c[1:],a));rp=mp.sqrt(2)*mp.fsum(-cn*an/(u-an)**2 for cn,an in zip(c[1:],a));du=r/rp;u-=du
 if abs(du)<mp.mpf('1e-165'):break
else:raise ValueError('LOW imaginary Newton failed')
eps=mp.mpf('1e-100');cc=[arb(s) for s in d['v_even0_low']];aa=[arb(n)**2/(arb(m)**2) for n in range(1,m+1)];weights=[arb(2).sqrt()*cn for cn in cc[1:]]
def f(x):return cc[0]+sum((w*x/(x-an) for w,an in zip(weights,aa)),arb(0))
l=f(arb(mp.nstr(u-eps,205)));r=f(arb(mp.nstr(u+eps,205)));assert (l>0 and r<0) or (l<0 and r>0)
p=Path(os.environ.get('GROUND_ROOT_BRACKET_OUTPUT',str(P/'low_bracket_validation_m300.json')));out=json.loads(p.read_text());row=next(q for q in out['rows'] if q['world']=='dh' and q['parity']=='even');assert row['passed']==299
row['checks'].append(dict(root_id=seed['root_id'],u_center=mp.nstr(u,180),u_halfwidth='1e-100',pole_free=True,opposite_endpoint_signs=True,status='PASS'));assert all(mp.mpf(q['u_center'])-u>2*eps for q in row['checks'] if q['root_id']!=seed['root_id']);row.update(brackets_attempted=300,passed=300,all_brackets_disjoint=True,complete_rounded_low_polynomial_real_root_census=True,supplemental_pure_imaginary_check=dict(low_z_im=mp.nstr(Omlo*mp.sqrt(-u),180),high_z_im=seed['z_im'],newton_steps=it+1,root_shift=mp.nstr(abs(Omlo*mp.sqrt(-u)-mp.mpf(seed['z_im'])),40),scope='The sole remaining pure-imaginary root lies beyond the primary |z| cutoff; independently low-vector Newton refined and sign-bracket validated in u. Bounded 2 CPU seconds.'));tmp=p.with_suffix('.supplementtmp');tmp.write_text(json.dumps(out,indent=2)+'\n');tmp.replace(p);print('DH even LOW complete300/300; imaginary |z|',mp.nstr(Omlo*mp.sqrt(-u),20),flush=True)
