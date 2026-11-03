"""Preserve first203 source nodes and extend the same ordered ζ census."""
from pathlib import Path
import csv
from flint import acb,ctx
P=Path(__file__).resolve().parent;ctx.prec=384
rows=list(csv.DictReader((P/'source_inputs/zeta_zeros_203.csv').open()))
assert len(rows)==203
rows +=[dict(k=k,gamma=z.imag.mid().str(110,radius=False))for k,z in enumerate(acb.zeta_zeros(204,98),204)]
with(P/'zeta_zeros.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=['k','gamma']);w.writeheader();w.writerows(rows)
print('Saved301 fixed decimal ordinates')
