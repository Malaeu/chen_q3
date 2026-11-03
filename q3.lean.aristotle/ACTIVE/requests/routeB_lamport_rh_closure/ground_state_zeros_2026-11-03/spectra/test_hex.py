import run as r,json,subprocess,hashlib
A,_=r.build(40,624)
def hx(x):
 d,e,_=x.digits(16);return ('-' if d[0]=='-' else '')+'0x0.'+d.lstrip('-')+'@'+str(e)
rows=[]
for w in ['zeta','dh','plant']:
 for par,B in zip(['even','odd'],A[w]):
  ans=[]
  for conv in [str,hx]:
   data=f'{len(B)} 600\n'+'\n'.join(conv(x) for x in B.flat)+'\n';s=json.loads(subprocess.run([str(r.P/'loweig')],input=data,text=True,capture_output=True,check=True).stdout);ans.append({k:s[k] for k in ['lambda','v','bisection_width']})
  assert ans[0]==ans[1],(w,par);rows.append(dict(world=w,parity=par,bitwise_equal_eigenpairs=True))
r.atomic(r.P/'hex_input_validation.json',dict(m=40,source_bits=624,solver_bits=600,rows=rows,scope='Exact binary base16 source serialization matches decimal roundtrip eigenvalues/eigenvectors/bisection widths bit-for-bit for all world/parity blocks'))
print('PASS',flush=True)
