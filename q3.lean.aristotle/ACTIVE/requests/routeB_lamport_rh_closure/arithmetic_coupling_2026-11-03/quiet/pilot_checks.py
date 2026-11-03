"""Direct normalized-evaluation annihilation on independent row/null pilots."""
from build import *

def main():
 for m in [16,80,248,300]:
  for world in ['zeta','dh']:
   g.get_context().precision=768;L=g.log(m);omega=2*g.const_pi()*m/L;ev=[x for x in events(world) if x[0]<omega];raw=rows(m,ev,L);normalized=[]
   for row in raw:
    scale=max(abs(t) for t in row);normalized.append([float(x/scale) for x in row])
   E=np.array(normalized);f=P/'frames'/f'{world}_m{m}.json';d=json.loads(f.read_text());Q=np.load(f.with_suffix('.npz'))['Q'];d['row_normalized_E_Q_relative_norm']=float(la.norm(E@Q,2)/la.norm(E,2));assert d['row_normalized_E_Q_relative_norm']<1e-12;f.write_text(json.dumps(d,indent=2)+'\n');print(world,m,d['row_normalized_E_Q_relative_norm'],flush=True)
if __name__=='__main__':main()
