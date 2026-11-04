"""400-bit pinned-source paired quadrature pilots; not interval certificates."""
from source_moments import *
def pilot(m):
 s=load();g=s.g;one=s.build(m,192);two=s.build(m,256);L=g.log(m);ds=[g.mpfr(1)]+[g.sqrt(2)]*m;z=g.mpc(2*s.pi/g.log(2),g.mpfr('.25'));e=[2*ds[j]*z*g.sin(z*L/2)/(g.sqrt(L)*(z*z-(2*s.pi*j/L)**2))for j in range(m+1)];W=np.array([[4*(a*b).real for b in e]for a in e],object);out=[]
 for w in ['zeta','dh','plant']:
  key='zeta'if w=='plant'else w;a=one[key]['A1']+(W if w=='plant'else 0);b=two[key]['A1']+(W if w=='plant'else 0);f1=sum((v*v for v in a.flat),g.mpfr(0));f2=sum((v*v for v in b.flat),g.mpfr(0));cache=json.loads((LOCAL/f'm{m}_q192.json').read_text());row=next(r for r in cache['rows']if r['world']==w)
  out.append(dict(world=w,m=m,source_bits=400,GL_orders=[192,256],MP_A_maxentry_difference=str(max(abs(v)for v in(b-a).flat)),MP_Frob2_q192=str(f1),MP_Frob2_q256=str(f2),MP_Frob2_difference=str(f2-f1),binary64_Frob2_minus_MP=str(g.mpfr(row['Frob2'])-f1)))
 p=OUT/f'SOURCE_MOMENTS_mp_m{m}.json';p.write_text(json.dumps(out,indent=2)+'\n');print('MP PILOT',m,out[0]['MP_A_maxentry_difference'],flush=True)
if __name__=='__main__':
 with ProcessPoolExecutor(max_workers=2)as ex:list(ex.map(pilot,[16,40,300]))
