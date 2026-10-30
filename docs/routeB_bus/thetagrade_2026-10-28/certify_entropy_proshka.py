#!/usr/bin/env python3
"""ENTROPY: elementary interval certificates; no floating quadrature, no Arb.
Run: uv run --with mpmath==1.3.0 python certify_entropy.py
Optional: add --m16 with the authoritative TXT in the current directory.
"""
from __future__ import annotations
import argparse
import hashlib
import math
import re
import time
from pathlib import Path
import mpmath as mp

EXPECTED = "5a636544b8a6b0ee52a6e212201df7cd5fa64c98d4021767b36dc7e67a4eabf1"
iv = mp.iv

def progress(i: int, n: int, start: float) -> None:
    done = i / n
    eta = (time.monotonic() - start) * (n - i) / max(i, 1)
    bar = "#" * int(24 * done) + "-" * (24 - int(24 * done))
    print(f"[{bar}] {i}/{n} ETA {eta:.1f}s", flush=True)

def theta_hr(x):
    """h and h''-h/4 on x>=0, with uniform n>=9 remainder."""
    y = iv.pi * iv.exp(2*x)
    pref = iv.exp(x/2)
    H, R = iv.mpf(0), iv.mpf(0)
    for n in range(1, 9):
        z = y * n*n
        e = pref * iv.exp(-z)
        H += 8*z*(2*z-3)*e
        R += 16*z*(4*z**3-28*z**2+41*z-9)*e
    H += iv.mpf([0, "1e-90"])
    R += iv.mpf([0, "1e-90"])
    return H, R

def theta_h(x):
    y = iv.pi*iv.exp(2*x)
    pref = iv.exp(x/2)
    return (pref*sum(8*(y*n*n)*(2*y*n*n-3)*iv.exp(-y*n*n)
                     for n in range(1,9)) + iv.mpf([0,"1e-90"]))

def moments() -> None:
    iv.dps = 45
    y = iv.pi * 81
    theta_tail = 3000*y**4*iv.exp(-y)
    assert theta_tail.b < iv.mpf("1e-90").a
    print("theta remainder upper:", theta_tail)
    panels = 4096
    step = iv.mpf(3)/(2*panels)  # exact dyadic mesh
    M2, M3, M4 = iv.mpf(0), iv.mpf(0), iv.mpf(0)
    g_lower = iv.mpf(0)
    start = time.monotonic()
    for i in range(panels):
        x = iv.mpf([(step*i).a, (step*(i+1)).b])
        H, R = theta_hr(x)
        assert H.a > 0
        g = R/H
        co = (iv.exp(x/2)+iv.exp(-x/2))/2
        rho = co*H
        M2 += step*rho*g**2
        M3 += step*co*R**3/H**2
        M4 += step*rho*g**4
        if g.a < g_lower.a:
            g_lower = g.a
        if (i+1) % 1024 == 0:
            progress(i+1, panels, start)
    tail = (iv.mpf(1600000000)*math.factorial(10)*iv.exp(-60)
            * sum(iv.mpf(60)**k/math.factorial(k) for k in range(11)))
    print("M2 core:", M2)
    print("M3 core:", M3)
    print("M4 core:", M4)
    print("M2/M4 common positive tail majorant:", tail)
    print("g lower on core:", g_lower)
    assert M3.a > 180000
    assert M2.b + tail.b < 2000
    assert M4.b + tail.b < 100000000
    assert g_lower.a > -100
    # Outside the core, R(z)>0 since z>=pi*exp(3)>60>7.
    eps = iv.mpf("0.001")
    gap_lower = (iv.mpf(2)/3*eps**3*180000
                 -eps**4*(iv.mpf(2)/3*100000000+2000**2))
    assert gap_lower.a > iv.mpf("0.00004").b
    print("CERTIFIED: M3>180000, M2<2000, M4<1e8, g>-100.")
    print("Ent(F^2)-E_h(F)/4 strict lower bound:", gap_lower)
    print("CERTIFIED EXPLICIT LSI COUNTEREXAMPLE epsilon=1/1000.")

def m16(path: Path) -> None:
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != EXPECTED:
        raise ValueError("Authoritative TXT SHA-256 mismatch")
    iv.dps = 100
    text = data.decode("utf-8")
    pairs = re.findall(r"^\d+ \[([^\s]+) \+/- ([^\]]+)\]", text, re.M)
    if len(pairs) != 17:
        raise ValueError("Expected exactly 17 even coordinates")
    def ball(a: str, r: str):
        ru = iv.mpf(r).b
        return iv.mpf(a)+iv.mpf([-ru, ru])
    X = [ball(a,r) for a,r in pairs]
    norm = iv.sqrt(sum(x*x for x in X))
    assert norm.a > 0
    X = [x/norm for x in X]
    lm = re.search(r"^lambda1=\[([^\s]+) \+/- ([^\]]+)\]", text, re.M)
    if lm is None:
        raise ValueError("Missing lambda1 ball")
    lam = ball(*lm.groups())
    L = iv.log(16); b = L/2; pi = iv.pi
    rt2 = iv.sqrt(2); rtL = iv.sqrt(L)
    B0 = (abs(X[0])+rt2*sum(abs(x) for x in X[1:]))/rtL
    B1 = rt2*sum(abs(X[j])*2*pi*j/L for j in range(1,17))/rtL
    B2 = rt2*sum(abs(X[j])*(2*pi*j/L)**2 for j in range(1,17))/rtL
    assert B0.b < 2 and B1.b < 11 and B2.b < 87
    print("Input norm:", norm)
    print("B0, B1, B2:", B0, B1, B2)
    panels = 4096
    dt = iv.mpf(1)/panels
    total = iv.mpf(0)
    start = time.monotonic()
    for i in range(panels):
        t = iv.mpf([(dt*i).a, (dt*(i+1)).b])
        x = b*t
        H = theta_h(x)
        v = (X[0]+rt2*sum(X[j]*iv.cos(2*pi*j*(x+b)/L)
                          for j in range(1,17)))/rtL
        total += 2*b*dt*H*v
        if (i+1) % 1024 == 0:
            progress(i+1,panels,start)
    product = lam*total
    assert total.a > iv.mpf(".0834").b
    assert total.b < iv.mpf(".0952").a
    assert product.a > iv.mpf("3.95e-33").b
    assert product.b < iv.mpf("4.51e-33").a
    print("<h,v>:", total)
    print("lambda1*<h,v>:", product)
    print("This certifies functions of INPUT BOXES, not a rerun of source eigenpair isolation.")
    yp = pi*65**2/16
    prime_tail = 128*L*2*pi**2/iv.mpf(4)**iv.mpf("4.5")*65**5*iv.exp(-yp)
    Y = pi*256
    arch_tail = 64*L*2*iv.exp(-b/2)*(Y+1)*iv.exp(-Y)
    a = pi*pi/(4*L)
    F_tail = 2*6000*1200/rtL*iv.exp(-a*161)/(1-iv.exp(-a))
    assert prime_tail.b < iv.mpf("9e-351").a
    assert arch_tail.b < iv.mpf("8e-345").a
    assert F_tail.b < iv.mpf("9e-56").a
    print("external prime tail:", prime_tail)
    print("external arch tail:", arch_tail)
    print("sampled F tail:", F_tail)
    print("D_ext NOT COMPUTED. No X=total-F substitution performed.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--m16", action="store_true")
    parser.add_argument("--only-m16", action="store_true")
    parser.add_argument("--request", type=Path,
                        default=Path("PROSHKA_REQUEST_ENTROPY_2026-10-30.txt"))
    args = parser.parse_args()
    if mp.__version__ != "1.3.0":
        raise RuntimeError("Reproduce with the pinned mpmath==1.3.0")
    if not args.only_m16:
        moments()
    if args.m16 or args.only_m16:
        m16(args.request)
