"""Collect replayed certificates without treating finite-basis positivity as proof."""
from pathlib import Path
import json,csv,shutil,os
from decimal import Decimal,localcontext
P=Path(__file__).resolve().parent
EXT=Path(os.environ.get('Q1_EXTERNAL_ROOT',str(P/'external_source')))
rows=[]
for a,T,N in [('4_5',200,200),('31_32',600,460)]:
 for parity in [0,1]:
  name=f'cert_L{a}_T{T}_N{N}_p{parity}.json';src=EXT/'weil_certificate/results'/name
  if not src.exists():src=P/('replayed_'+name)
  if src.exists():
   dst=P/('replayed_'+name)
   if src.resolve()!=dst.resolve():shutil.copyfile(src,dst)
   d=json.loads(dst.read_text());up=json.loads((P/('upstream_'+name)).read_text());value=lambda v: Decimal(v.strip('[]').split()[0]);rel=abs((value(d['lam_lower'])-value(up['lam_lower']))/value(up['lam_lower']));rows.append(dict(name=name,status='REPRODUCED' if d['ok'] and rel<Decimal('1e-12') else 'DISCREPANCY',lam_lower=d.get('lam_lower'),relative_difference=str(rel),relative_tolerance='1e-12',exact_lower_string_match=d.get('lam_lower')==up.get('lam_lower')))
  else:rows.append(dict(name=name,status='RUNNING'))
validation=[]
a=P/'our_N32_dps130.json';b=P/'our_N32_dps160.json'
if a.exists() and b.exists():
 with localcontext() as ctx:
  ctx.prec=90
  for x,y in zip(json.loads(a.read_text()),json.loads(b.read_text())):
   validation.append(dict(label=x['label'],relative_even_difference=str(abs((Decimal(x['even'])-Decimal(y['even']))/Decimal(y['even']))),relative_odd_difference=str(abs((Decimal(x['odd'])-Decimal(y['odd']))/Decimal(y['odd'])))))
report=dict(route='CHALLENGER / NOT_RH',status='DIAGNOSTIC_NEVER_A_PROOF',external_certificates=rows,our_fixed_basis_validation=validation,validation_note='Differences compare saved80-significant-digit strings, not exact underlying arithmetic; zeros mean agreement at printed precision.',P2={'negative_witness_arb':'REPRODUCED','positive_continuum_lower_certificate':'UPSTREAM_SOURCE_ONLY_NOT_RERUN','independent_scalar_sign_flip':'W=1.114 positive; W=1.1147 negative; not a positivity proof at low endpoint'},caveat='Our cosine/sine bases N16 and32 do not resolve P2 negative ground state; the independent polynomial witness does. Finite-basis positive minima and ratios do not establish full-space positivity or exact continuum ratios.')
(P/'SUMMARY.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
