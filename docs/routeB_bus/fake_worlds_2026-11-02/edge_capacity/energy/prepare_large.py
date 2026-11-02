"""Source-correct finite A/head materialization for saved large edge-law vectors.

No source eigensystem or zero search. Reuses the pinned edge_rellich source
moment helper; all source terms and exact arch tail are retained.
"""
from pathlib import Path
import argparse,json,csv,hashlib,importlib.util,time,tempfile
import mpmath as mp
import energy_split
P=Path(__file__).resolve().parent

def erow(z,m,L):
 b=L/2;out=[]
 for n in range(m+1):
  om=2*mp.pi*n/L;dn=1 if n==0 else mp.sqrt(2)
  out.append(dn*(-1)**n*b/mp.sqrt(L)*(mp.sinc((z-om)*b)+mp.sinc((z+om)*b)))
 return out

def prepare(path,helper,zeta_zeros,dh_zeros,work,order=192,build_dps=150):
 start=time.monotonic();path=Path(path);raw=path.read_bytes();d=json.loads(raw);m=int(d['m']);world=d['world'].lower();T=mp.mpf(d['T'])
 spec=importlib.util.spec_from_file_location('pinned_rellich_source_helper',helper);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 mp.mp.dps=build_dps;T=mp.mpf(d['T']);L=mp.log(m)
 A,*_=module.build(m,world,order);rows=[];signs=[]
 zpath=Path(zeta_zeros if world=='zeta' else dh_zeros);zbytes=zpath.read_bytes()
 if world=='zeta':
  for r in csv.DictReader(zpath.open()):
   g=mp.mpf(r['gamma'])
   if g<T:rows.append(erow(g,m,L));signs.append(1)
 else:
  z=json.loads(zbytes)
  for r in z['critical_line_zeros']:
   g=mp.mpf(r['gamma'])
   if g<T:rows.append(erow(g,m,L));signs.append(1)
  for r in z['off_line_pairs']:
   g=mp.mpf(r['gamma']);dd=mp.mpf(r['sigma_right'])-mp.mpf('.5')
   if g<T:
    v=erow(g+mp.j*dd,m,L)
    rows.extend([[mp.sqrt(2)*mp.re(x) for x in v],[mp.sqrt(2)*mp.im(x) for x in v]]);signs.extend([1,-1])
 assert len(rows)==int(d['q']),('Head cardinality changed',world,m,len(rows),d['q'])
 f=d.get('complement_f',d.get('physical_modal_coefficients'))
 if f is None:raise KeyError('Saved physical selected vector absent')
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=m,N=m,world=world,dps=build_dps,L=L,T=T,q=len(rows),rank=d.get('rank',len(rows)),cutoff_mode=d.get('cutoff_mode',d.get('mode')),A=A,E=mp.matrix(rows),row_signs=signs,complement_f=f,complement_minimum=d['complement_minimum'],materialization=dict(source_vector_file=path.name,source_vector_sha256=hashlib.sha256(raw).hexdigest(),source_vector_dps=d.get('dps'),source_helper_file=Path(helper).name,source_helper_sha256=hashlib.sha256(Path(helper).read_bytes()).hexdigest(),zero_table_file=zpath.name,zero_table_sha256=hashlib.sha256(zbytes).hexdigest(),quadrature_order=order,build_dps=build_dps,new_eigensystems=0,new_zero_searches=0,source_head_includes_signed_DH_complex_pairing=True))
 work=Path(work);work.mkdir(parents=True,exist_ok=True);p=work/(world+'_'+path.stem+f'_A_gl{order}.json');p.write_text(json.dumps(energy_split.serial(out,digits=build_dps),indent=2)+'\n')
 label=world+'_'+path.stem+(f'_gl{order}' if order!=192 else '')
 result=energy_split.serial(energy_split.run(p,label=label,low_dps=max(build_dps+30,180)),digits=max(build_dps+70,220));result['materialization']=energy_split.serial(out['materialization']);result['materialization_seconds']=time.monotonic()-start
 result['new_matrix_builds']=1
 result['operator_source']='Rebuilt unchanged full original finite source at fixed m on the frozen saved selected vector; no eigensystem'
 result['method']='Rebuilt full source constant/cross/volume bilinear pieces minus finite actual signed low-zero head; not an independent infinite zero-tail sum'
 destination=P/('energy_'+label+'.json');destination.write_text(json.dumps(result,indent=2)+'\n')
 return result

if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('source');a.add_argument('--helper',default=str(P.parents[1]/'edge_rellich'/'rellich.py'));a.add_argument('--zeta-zeros',default=str(P.parents[2]/'capacity_matrix_2026-11-02'/'zeros.csv'));a.add_argument('--dh-zeros',default=str(P.parents[1]/'edge_law'/'dh'/'dh_zeros_extended.json'));a.add_argument('--work',default=str(Path(tempfile.gettempdir())/'edge_energy_source_materialized'));a.add_argument('--order',type=int,default=192);a.add_argument('--build-dps',type=int,default=150);args=a.parse_args();prepare(args.source,args.helper,args.zeta_zeros,args.dh_zeros,args.work,args.order,args.build_dps)
