import run,json,sys,time,traceback
parity=int(sys.argv[1]);start=time.monotonic();done=0
for m in range(16,301):
 if m%2!=parity:continue
 paths=[run.V/f'{w}_m{m}.json' for w in ['zeta','dh','plant']]
 if all(p.exists() and json.loads(p.read_text()).get('v_even0_low') is not None and 'FT_precision_ok' in json.loads(p.read_text()) for p in paths):continue
 try:run.run(m);done+=1
 except Exception as ex:run.atomic(run.P/f'failure_m{m}.json',dict(m=m,status='FAILED_NO_GROUND_CLAIM',error=str(ex),traceback=traceback.format_exc()));print('FAILED',m,repr(ex),flush=True)
run.atomic(run.P/f'shard{parity}_complete.json',dict(parity=parity,cells_computed=done,seconds=time.monotonic()-start))
