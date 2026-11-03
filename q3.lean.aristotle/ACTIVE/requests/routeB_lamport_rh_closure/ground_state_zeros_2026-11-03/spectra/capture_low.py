import run as r
import json,sys,math
m=int(sys.argv[1]);b0=6*m+256;A,meta=r.build(m,b0);Llow=str(r.g.log(m));f=r.F
for w in ['zeta','dh','plant']:
 path=r.V/f'{w}_m{m}.json';row=json.loads(path.read_text());s=[]
 for i,B in enumerate(A[w]):
  bits=row['blocks'][i]['solver_bits_low'];s.append(r.solve(B,bits))
  block=row['blocks'][i];gap=f(block['gap']);scale=max(f(1),max(abs(x) for x in B.flat));rr=r.g.sqrt(len(B))*f(block['residual_infinity'][0]);eb=f(2)**(-block['solver_bits_high']+24)*scale
  block['vector0_high_error_heuristic_l2']=str(2*(rr+eb)/gap);block['vector0_replay_l2_upper']=str(r.g.sqrt(len(B))*f(block['vector_replay_infinity'][0]));v0=list(map(f,block['v0']));v1=list(map(f,block['v1']));block['low_two_orthogonality']=str(abs(sum((x*y for x,y in zip(v0,v1)),f(0))))
 row['L_low']=Llow;row['v_even0_low']=[str(x) for x in s[0]['v'][0]];row['v_odd0_low']=[str(x) for x in s[1]['v'][0]];row['low_precision_dps']=min(x['bits'] for x in s)*math.log10(2)//1
 L=f(row['L']);T=(1+f('.25')*(1+r.g.log(L))/L)*2*r.g.const_pi()*m/L;err=r.g.sqrt(L)*f(row['blocks'][0]['vector0_high_error_heuristic_l2']);H=r.g.exp(-r.g.const_pi()*T/4)
 row.update(T=str(T),even_FT_real_axis_absolute_error_heuristic=str(err),nominal_H_exponential_scale_at_T=str(H),FT_precision_margin_ratio=str(err/H),FT_precision_ok=bool(err<H*f('1e-20')),low_coordinates_captured_by_independent_rebuild=True)
 r.atomic(path,row);print(w,m,'captured',flush=True)
