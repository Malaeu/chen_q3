"""Postprocess saved step profiles; float summaries only."""
import csv
from pathlib import Path
p=Path(__file__).resolve().parent
r=list(csv.DictReader((p/'profiles.csv').open()));b=list(csv.DictReader((p/'budgets.csv').open()));out=[]
for budget in b:
    w=[float(x['f']) for x in r if all(x[k]==budget[k] for k in ['world','mesh','t'])]
    h=1/int(budget['mesh']);norm=sum(v*v*h for v in w)
    out.append(dict(world=budget['world'],mesh=budget['mesh'],t=budget['t'],history_negative_index=budget['past_negative_index'],terminal_bin_mass_fraction=h/norm,first_quarter_mass_fraction=sum(v*v*h for v in w[:len(w)//4])/norm,last_quarter_mass_fraction=sum(v*v*h for v in w[len(w)*3//4:])/norm,sign_changes=sum(w[i]*w[i+1]<0 for i in range(len(w)-1)),max_abs=max(abs(v) for v in w)))
with (p/'shape.csv').open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=out[0]);writer.writeheader();writer.writerows(out)
