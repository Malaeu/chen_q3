"""Read saved screen only; no calls to any source builder or eigensystem."""
from pathlib import Path
import json,csv,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;Q=P.parent;mp.mp.dps=70
TARGETS=['85.6993484854','114.1633427308','240.4046723514','166.4793059132'];MS=[74,75,206,207,621,622,2000]

def main():
 raw=(Q/'INPUT_events.csv').read_bytes();blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();assert blob=='364281a907e0da23aafeab6d442407ba68c2a01a'
 ev=list(csv.DictReader(raw.decode().splitlines()));lookup={(int(r['m']),int(r['j'])):r for r in ev};assert len(ev)==len(lookup)==18811
 saved=json.loads((Q/'INPUT_screen_summary.txt').read_text());assert saved['events']['count']==len(ev)
 census=json.loads((Q/'INPUT_census.txt').read_text());summary=[];neighbors=[]
 for gamma in TARGETS:
  pair=min(census['off_line_pairs'],key=lambda r:abs(mp.mpf(r['gamma'])-mp.mpf(gamma)))
  for m in MS:
   L=mp.log(m);step=2*mp.pi/L;x=mp.mpf(gamma)/step;j0=int(mp.nint(x));full=int(mp.nint(mp.mpf(pair['gamma'])/step));assert j0==full
   valid=[j for j in [j0-1,j0,j0+1]if 1<=j<=m];hits=[]
   for j in valid:
    event=lookup.get((m,j));hit=event is not None
    if hit:hits.append(j)
    neighbors.append(dict(address_gamma=gamma,m=m,j0=j0,j=j,offset=j-j0,omega=mp.nstr(step*j,24),target_distance_steps=mp.nstr(abs(mp.mpf(j)-x),24),saved_event=hit,negative_diagonal=event['negative_diagonal']if hit else'',failed_minor=event['failed_minor']if hit else'',saved_Ajj=event['Ajj']if hit else'',saved_minor_det=event['minor_det']if hit else'',saved_nearest_off_gamma=event['off_gamma']if hit else'',saved_nearest_off_distance_steps=event['off_distance_steps']if hit else'',status='SAVED_EVENT'if hit else'NO_SAVED_EVENT'))
   summary.append(dict(address_gamma=gamma,census_gamma=pair['gamma'],sigma_right=pair['sigma_right'],m=m,L=mp.nstr(L,24),grid_step=mp.nstr(step,24),j0=j0,valid_neighbors=valid,event_j=hits,event_count=len(hits),address_admitted=bool(valid),half_integer_distance=mp.nstr(abs(x-(mp.floor(x)+mp.mpf(1)/2)),24)))
 result=dict(status='SAVED_SCREEN_ONLY_DIAGNOSTIC_NOT_A_THRESHOLD_LAW',source_events_git_blob=blob,source_saved_event_count=len(ev),source_screen_summary_status=saved['status'],selected_m=MS,address_count=4,summary_rows=summary,neighbor_rows_count=len(neighbors),no_source_or_matrix_recomputation=True,absence_semantics='No matching (m,j) row in the frozen failure-event CSV; not an independently computed nonnegative margin.',C4_addresses_with_hit_at_m2000=sum(r['event_count']>0 for r in summary if r['m']==2000))
 (P/'ADDRESS_MATCHES.json').write_text(json.dumps(result,indent=2)+'\n')
 with(P/'ADDRESS_NEIGHBORS.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=list(neighbors[0]));w.writeheader();w.writerows(neighbors)
 compact=[]
 for r in summary:compact.append({k:(','.join(map(str,r[k]))if isinstance(r[k],list)else r[k])for k in ['address_gamma','m','j0','valid_neighbors','event_j','event_count']})
 with(P/'ADDRESS_TABLE.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=list(compact[0]));w.writeheader();w.writerows(compact)
 print('neighbors',len(neighbors),'C4',result['C4_addresses_with_hit_at_m2000'])
 for gamma in TARGETS:print(gamma,[(r['m'],r['j0'],r['valid_neighbors'],r['event_j'])for r in summary if r['address_gamma']==gamma])
if __name__=='__main__':main()
