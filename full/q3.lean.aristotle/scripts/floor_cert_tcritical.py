#!/usr/bin/env python3
import math
from datetime import datetime

import mpmath as mp

# Certificate for P_A floor at t_critical on Icc(-1/2, 1/2)
# Grid + Lipschitz (finite difference) estimate.

mp.mp.dps = 60

B_min = mp.mpf(3)
t_critical = mp.mpf(3) / mp.mpf(20)  # 0.15

# grid step
h = mp.mpf(1) / mp.mpf(4000)  # 0.00025

# margins
L_margin = mp.mpf("1.10")  # 10% safety factor

# functions
pi = mp.pi


def a(xi: mp.mpf) -> mp.mpf:
    z = mp.mpf("0.25") + 1j * pi * xi
    return mp.log(pi) - mp.re(mp.digamma(z))


def w(B: mp.mpf, t: mp.mpf, xi: mp.mpf) -> mp.mpf:
    lin = 1 - abs(xi) / B
    if lin <= 0:
        return mp.mpf(0)
    return lin * mp.e ** (-4 * pi**2 * t * xi**2)


def g(B: mp.mpf, t: mp.mpf, xi: mp.mpf) -> mp.mpf:
    return a(xi) * w(B, t, xi)


def P_A(B: mp.mpf, t: mp.mpf, theta: mp.mpf) -> mp.mpf:
    # support |theta + m| <= B => m in [ceil(-B-theta), floor(B-theta)]
    m_min = int(mp.ceil(-B - theta))
    m_max = int(mp.floor(B - theta))
    s = mp.mpf(0)
    for m in range(m_min, m_max + 1):
        s += g(B, t, theta + m)
    return 2 * pi * s


# grid evaluation
N = int(mp.nint((mp.mpf(1) / h)))  # number of steps across length 1

vals = []

theta0 = mp.mpf(-0.5)
for i in range(N + 1):
    theta = theta0 + h * i
    vals.append(P_A(B_min, t_critical, theta))

min_grid = min(vals)

# finite difference derivative estimate
# central differences for interior points
max_deriv = mp.mpf(0)
for i in range(1, N):
    d = (vals[i + 1] - vals[i - 1]) / (2 * h)
    ad = abs(d)
    if ad > max_deriv:
        max_deriv = ad

L_ub = max_deriv * L_margin

# choose rational-ish bounds
# min_lb: round down to 3 decimals
min_lb = mp.floor(min_grid * 1000) / 1000
# L_ub: round up to 1 decimal
L_ub_up = mp.ceil(L_ub * 10) / 10

cert_margin = min_lb - L_ub_up * h / 2

# output
stamp = datetime.now().strftime("%Y-%m-%d_%H%M")
print("floor_cert_tcritical", stamp)
print("B_min", B_min)
print("t_critical", t_critical)
print("grid_step_h", h)
print("min_grid", min_grid)
print("min_lb", min_lb)
print("max_deriv", max_deriv)
print("L_ub_up", L_ub_up)
print("cert_margin", cert_margin)

out_dir = "/Users/emalam/Documents/GitHub/chen_q3/sandboxes/projekt_2/full/q3.lean.aristotle/output"
# write summary file
out_path = f"{out_dir}/floor_cert_tcritical_{stamp}.txt"
with open(out_path, "w", encoding="utf-8") as f:
    f.write(f"floor_cert_tcritical {stamp}\n")
    f.write(f"B_min = {B_min}\n")
    f.write(f"t_critical = {t_critical}\n")
    f.write(f"grid_step_h = {h}\n")
    f.write(f"min_grid = {min_grid}\n")
    f.write(f"min_lb = {min_lb}\n")
    f.write(f"max_deriv = {max_deriv}\n")
    f.write(f"L_ub_up = {L_ub_up}\n")
    f.write(f"cert_margin = {cert_margin}\n")

print("wrote", out_path)

# write grid values (audit)
grid_path = f"{out_dir}/floor_grid_tcritical_{stamp}.txt"
with open(grid_path, "w", encoding="utf-8") as f:
    f.write(f"floor_grid_tcritical {stamp}\n")
    f.write(f"B_min = {B_min}\n")
    f.write(f"t_critical = {t_critical}\n")
    f.write(f"grid_step_h = {h}\n")
    f.write("i\ttheta\tP_A\n")
    theta = theta0
    for i, v in enumerate(vals):
        f.write(f"{i}\t{theta}\t{v}\n")
        theta += h

print("wrote", grid_path)
