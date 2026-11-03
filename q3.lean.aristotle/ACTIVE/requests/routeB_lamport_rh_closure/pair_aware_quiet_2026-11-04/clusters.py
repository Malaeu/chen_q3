from common import *
rows=[]
for(w,m),d in dataset().items():
 for theta in THETAS:
  ps=sorted(pairs_for(w,m,theta),key=lambda x:x['left_ordinal']);groups=[]
  for p in ps:
   if groups and groups[-1][-1]['right_ordinal']==p['left_ordinal']:groups[-1].append(p)
   else:groups.append([p])
  for i,g in enumerate(groups):rows.append(dict(world=w,m=m,theta=theta,cluster_id=i,first_ordinal=g[0]['left_ordinal'],last_ordinal=g[-1]['right_ordinal'],height_events=len(g)+1,real_constraint_rows=g[0]['left_mult']+sum(x['right_mult']for x in g),first_gamma=g[0]['left_gamma'],last_gamma=g[-1]['right_gamma'],forbidden_q=' '.join(str(x['split_q'])for x in g),overlapping_pair_cluster=len(g)>1))
write_csv('CLUSTERS.csv',rows);print(len(rows),'connected markededgeclusters;',sum(x['height_events']>=3 for x in rows),'of3+events')
