"""Directed serialization helpers (CLASSFLOOR 2.5 / NOTES.md items 2 and 3).

`arb_get_str` guarantees last-decimal accuracy, NOT outward rounding, so a radius-free
printed decimal is not a directed endpoint.  Everything exported from this run as a
*number a human or a later script may use as a bound* goes through `dec_lower` /
`dec_upper`, which emit a decimal string whose ball-arithmetic comparison against the
source ball has been VERIFIED:

    arb(dec_lower(x)) <  x   (so the string is a true lower bound for inf(x))
    arb(dec_upper(x)) >  x   (so the string is a true upper bound for sup(x))

python-flint's `<` / `>` on arb are certified relations: they return True only when the
inequality holds for every pair of points in the two balls.  Both helpers are SIGNED and
sign-agnostic; `abs_lower` is never used as a signed lower endpoint (NOTES.md item 3).
"""
from fractions import Fraction
from flint import arb, ctx


def _cand(v, digits):
    return ("%." + str(digits) + "e") % v


def dec_lower(x, digits=17):
    """decimal string L with arb(L) < x, certified."""
    m = float(x.mid().str(30, radius=False))
    r = float(x.rad().str(30, radius=False))
    v = m - r
    slack = max(abs(v), 1e-300) * 1e-15 + 1e-320
    for _ in range(200):
        s = _cand(v - slack, digits)
        if arb(s) < x:
            return s
        slack *= 2
    raise RuntimeError("dec_lower failed")


def dec_upper(x, digits=17):
    """decimal string U with arb(U) > x, certified."""
    m = float(x.mid().str(30, radius=False))
    r = float(x.rad().str(30, radius=False))
    v = m + r
    slack = max(abs(v), 1e-300) * 1e-15 + 1e-320
    for _ in range(200):
        s = _cand(v + slack, digits)
        if arb(s) > x:
            return s
        slack *= 2
    raise RuntimeError("dec_upper failed")


def rat_lower(x, den=10 ** 12):
    """rational p/den with p/den <= inf(x), certified; returns (p, den, string)."""
    m = float(x.mid().str(30, radius=False))
    r = float(x.rad().str(30, radius=False))
    import math
    p = math.floor((m - r) * den)
    while not (arb(p) / den < x):
        p -= 1
    return p, den, f"{p}/{den}"


def signed_interval(x, digits=17):
    """(L, U) certified directed decimal endpoints of the ball x."""
    return dec_lower(x, digits), dec_upper(x, digits)


def selftest():
    ctx.prec = 400
    ok = True
    for v in ("0", "1", "-1", "1e-30", "-1e-30", "3.14159265358979", "-2.718281828e12"):
        for rad in ("0", "1e-20", "1e-3"):
            b = arb(v, arb(rad))
            L = dec_lower(b); U = dec_upper(b)
            ok &= bool(arb(L) < b) and bool(arb(U) > b)
    return ok


if __name__ == '__main__':
    print("legser selftest:", selftest())
    ctx.prec = 400
    b = arb("-0.0012345678901234", arb("2.5e-9"))
    print("ball      ", b.str(20))
    print("dec_lower ", dec_lower(b))
    print("dec_upper ", dec_upper(b))
    print("rat_lower ", rat_lower(b)[2])
