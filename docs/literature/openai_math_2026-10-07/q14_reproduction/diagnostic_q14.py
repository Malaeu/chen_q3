#!/usr/bin/env python3
"""Finite contour and actual-xi diagnostics; NOT interval certificates."""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp
mp.mp.dps=45
lam=mp.mpf(1)/32
a2=lam*(lam+2)
p=mp.mpf(5)/4;q=mp.mpf(3)/2;c=mp.mpf(3)/4
kap=lambda z:-2*z/(z*z-a2)
Z=lambda z:(z*z-a2)/(z*z+2*z-a2)
a=kap(p);b=kap(q);res=-mp.mpf(1)/33

def phi(z,sector):
    ap=(a*p-z)/(p*(p*p-z*z));aq=(b*q-z)/(q*(q*q-z*z))
    bp=(p-a*z)/(p*(p*p-z*z));bq=(q-b*z)/(q*(q*q-z*z))
    return 2*(bp*bq-ap*aq) if sector=='++' else -2*(bp*bq+ap*aq)
rows=[]
for sector in ['++','+-']:
    f=lambda z:Z(z)*phi(z,sector)
    pole=res*phi(lam,sector)
    for Y in [mp.mpf(2)/5,mp.mpf(7)/10,mp.mpf(11)/10]:
        left=mp.quad(lambda y:f(1j*y),[-Y,0,Y])/(2*mp.pi)
        right=mp.quad(lambda y:f(c+1j*y),[-Y,0,Y])/(2*mp.pi)
        # Clockwise contour, left up; top right; right down; bottom left.
        horizontal=(mp.quad(lambda s:f(s+1j*Y),[0,c])-mp.quad(lambda s:f(s-1j*Y),[0,c]))/(2*mp.pi*1j)
        err=abs((right-left)-(pole+horizontal))
        omitted=abs((right-left)-pole)
        assert err<mp.mpf('1e-35')
        assert omitted>mp.mpf('1e-8')
        rows.append({'kind':'RATIONAL_CONTROL_NOT_XI','sector':sector,'Y':str(Y),
                     'identity_error':mp.nstr(err,16),'error_if_horizontal_dropped':mp.nstr(omitted,16),
                     'signed_pole_term':mp.nstr(pole,16)})

# Use actual xi only to calibrate the multiplier normalization and the proved exterior domain.
def F(z):
    s=mp.mpf('0.5')+z
    return s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)/2
for y in [mp.mpf('0.25'),mp.mpf('2.5'),mp.mpf('9')]:
    z=1j*y
    val=F(z); der=mp.diff(F,z)
    R=val/(val+der)
    X=mp.re(val); Xp=mp.re(1j*der)
    beta=X/(X-1j*Xp)
    err=abs(R-beta)
    assert err<mp.mpf('1e-35')
    assert abs(R)<=1+mp.mpf('1e-35')
    outer=F(c+1j*y)/(F(c+1j*y)+mp.diff(F,c+1j*y))
    assert abs(outer)<1
    rows.append({'kind':'ACTUAL_XI_POINT_DIAGNOSTIC_NOT_GLOBAL_CERTIFICATE',
                 'y':str(y),'boundary_error':mp.nstr(err,16),
                 'boundary_abs_R':mp.nstr(abs(R),16),'exterior_abs_R':mp.nstr(abs(outer),16)})
out={'status':'PASS_NONINTERVAL_DIAGNOSTICS','decimal_digits':mp.mp.dps,
     'cases':len(rows),'mpmath_version':mp.__version__,'rows':rows,
     'actual_xi_poles_computed':False,'full_CCM_spectrum_computed':False}
Path(__file__).with_name('diagnostic_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
