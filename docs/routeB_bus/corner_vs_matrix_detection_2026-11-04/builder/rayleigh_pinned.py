"""Fresh pinned MPFR matrix Rayleigh witness, not an eigenvalue ordering proof.

Full original builder is deliberately limited to m<=1000 unless the caller
explicitly raises max_m. This helper never assembles a zero-side Gram or clips.
"""
from fractions import Fraction
import importlib.util
import sys
import time
import numpy as np
from source_float import verify_source, SOURCE_PATH, SOURCE_SHA256, SOURCE_GIT_BLOB


def evaluate(m, vector, *, a=None, gamma=None, bits=256, max_m=1000):
    """Return JSON-serializable high-precision source/plant Rayleigh values.

    vector contains fixed binary64 coefficients; each is promoted exactly to
    MPFR. a accepts Fraction(1,3) or '1/3' for the exact rational convention.
    gamma accepts an integer/decimal string; require bits>=200 (60 decimal
    digits). Includes Q=4 Re(c c^T) only when both a and gamma are supplied.
    Returned sign is numerical evidence, not a rigorous interval certificate.
    """
    if bits < 200:raise ValueError('bits>=200 required (at least60 decimal digits)')
    if m>max_m:raise ValueError('full pinned builder cap exceeded; explicit budget decision needed')
    if (a is None)!=(gamma is None):raise ValueError('provide both a and gamma')
    v=np.asarray(vector,dtype=np.float64)
    if v.shape!=(m+1,) or not np.all(np.isfinite(v)):raise ValueError('invalid fixed physical-basis vector')
    verify_source()
    sys.path.insert(0,'/workspace/conditioning_deps')
    import gmpy2 as g
    spec=importlib.util.spec_from_file_location('_fresh_pinned_source',SOURCE_PATH)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    start=time.perf_counter();cpu=time.process_time()
    out,meta=module.build(m,bits)
    g.get_context().precision=bits+40
    vv=[g.mpfr(float(x)) for x in v]
    zero=g.mpfr(0)
    norm=sum((x*x for x in vv),zero)
    if norm==0:raise ValueError('zero vector')
    E=out['zeta'][0]
    source=sum((vv[i]*sum((E[i,j]*vv[j] for j in range(m+1)),zero) for i in range(m+1)),zero)
    plant=zero
    if a is not None:
        def real(x):
            if isinstance(x,Fraction):return g.mpfr(x.numerator)/x.denominator
            if isinstance(x,str) and '/' in x:return real(Fraction(x))
            # Decimal strings preserve decimal intent; float inputs mean exact binary floats.
            return g.mpfr(x)
        alpha=real(a);height=real(gamma);z=g.mpc(height,alpha)
        L=g.log(m);pi=g.const_pi();ss=g.sin(z*L/2);sqrtL=g.sqrt(L)
        projected=g.mpc(0)
        for j in range(m+1):
            d=g.mpfr(1) if j==0 else g.sqrt(2)
            w=2*pi*j/L
            if z*z==w*w:
                c=sqrtL if j==0 else d*sqrtL*((-1)**j)/2
            else:c=2*d*z*ss/(sqrtL*(z*z-w*w))
            projected+=vv[j]*c
        plant=4*(projected*projected).real
    digits=int(bits*.30103)+8
    def fmt(x):return format(x,f'.{digits}g')
    return dict(m=m,bits=bits,working_bits=bits+40,
                source_rayleigh=fmt(source/norm),plant_rayleigh=fmt(plant/norm),
                total_rayleigh=fmt((source+plant)/norm),vector_squared_norm=fmt(norm),
                total_negative=bool(source+plant<0),source_sha256=SOURCE_SHA256,
                source_git_blob=SOURCE_GIT_BLOB,source_meta=meta,
                wall_seconds=time.perf_counter()-start,cpu_seconds=time.process_time()-cpu,
                interval_certificate=False,kind='fixed-vector Rayleigh witness only',
                honesty='DIAGNOSTIC_NEVER_A_PROOF; CHALLENGER_NOT_RH')
