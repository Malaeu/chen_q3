import csv
from identify import *
rows=list(csv.DictReader((OUT/'ratios_grid.csv').open()))
rr=[r for r in rows if r['m']=='20'][::2]
A=mp.matrix([[mp.mpf(r['H'])*z for z in cheb(2*(mp.mpf(r['t'])/40)**2-1,15)] for r in rr])
G=A.T*A
conditions={}
for d in (0,1,2,3,4,5,6,7,10,15):
 ev=mp.eigsy(G[:d+1,:d+1],eigvals_only=True)
 conditions[2*d]=fmt(ev[len(ev)-1]/ev[0])
rows=list(csv.DictReader((OUT/'polynomial_fits.csv').open()))
for r in rows:r['normal_matrix_condition']=conditions[int(r['polynomial_degree_in_t'])]
csvout('polynomial_fits.csv',rows)
print(conditions)
