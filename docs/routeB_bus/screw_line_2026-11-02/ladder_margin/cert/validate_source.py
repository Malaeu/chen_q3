"""Independent MP source controls and nested interval-pivot replay.

Nearest-rounded MP numbers here are diagnostics only. Certification is
performed solely by the directed verifier, without these controls.
"""
from pathlib import Path
from fractions import Fraction
import sys,json,csv
import mpmath as mp
from certify import source,arb,ctx,BACKEND
P=Path(__file__).resolve().parent
core=P.parents[1]/'innovation_law'/'core';sys.path.insert(0,str(core))
from scan import source as mp_source
ctx.prec=512;mp.mp.dps=80;g,_=source(32,7);ref,_=mp_source('zeta',mp.mpf(3))
controls=[]
for k,r in [(1,Fraction(1)),(0,Fraction(2)),(0,Fraction(3)),(32,Fraction(1)),(0,Fraction(5)),(0,Fraction(7)),(-1,Fraction(2,3))]:
    t=mp.mpf(k)/32+mp.log(mp.mpf(r.numerator)/r.denominator)
    expected=ref(t);interval=g(k,r);inside=interval.contains(arb(mp.nstr(expected,80)))
    assert inside
    controls.append(dict(k=k,ratio=str(r),source_interval=interval.str(90),mp80_reference=mp.nstr(expected,80),reference_contained=inside))
low=list(csv.DictReader((P/'W3_M32_b512_pivots.csv').open()));high=list(csv.DictReader((P/'W3_M32_b768_pivots.csv').open()))
assert len(low)==len(high)==49
nested=[]
for a,b in zip(low,high):
    outer=arb(a['pivot_interval']);inner=arb(b['pivot_interval'])
    assert outer.contains(inner)
    nested.append(dict(index=int(a['index']),higher_precision_interval_contained=True))
result=dict(status='SOURCE_CONTROLS_AND_INTERVAL_REPLAY_PASSED',diagnostic='DIAGNOSTIC_NEVER_A_PROOF / CHALLENGER / NOT_RH',backend=BACKEND,source_controls=controls,pivot_replay=nested,warning='MP80 references validate normalization but do not provide certification. Higher-accuracy directed intervals are included in the512-bit pivot intervals.')
(P/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: seven independent source controls and49nested pivot intervals')
