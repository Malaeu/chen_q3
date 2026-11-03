import run as r,time,subprocess,json
out,_=r.build(160,1344);A=out['dh'][0];bits=640;n=len(A)
def hx(x):
 d,e,_=x.digits(16);return ('-' if d[0]=='-' else '')+'0x0.'+d.lstrip('-')+'@'+str(e)
for kind,conv in [('decimal',str),('hex',hx)]:
 t=time.monotonic();data=f'{n} {bits}\n'+'\n'.join(conv(x) for x in A.flat)+'\n';ser=time.monotonic()-t;t=time.monotonic();out=subprocess.run([str(r.P/'loweig')],input=data,text=True,capture_output=True,check=True);ans=json.loads(out.stdout);print(kind,'serialize',ser,'inputchars',len(data),'wall',time.monotonic()-t,'solveCPU',ans['seconds'],'lambda',ans['lambda'][0][:50],flush=True)
