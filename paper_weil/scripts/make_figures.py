#!/usr/bin/env python3
"""Figures for the Weil-positivity structure paper. All numbers computed here from definitions,
except the finite-window bottoms (Fig. 3) and trial constants (Fig. 4), which are copied from the
arb-certified caches recorded in docs/Progress_Log.md (2026-09-04/05)."""
import numpy as np, mpmath as mp, matplotlib
matplotlib.use("Agg"); import matplotlib.pyplot as plt
mp.mp.dps = 30
OUT = "paper_weil/figures/"
plt.rcParams.update({"font.size": 9, "figure.dpi": 200, "axes.spines.top": False, "axes.spines.right": False})

# ---- Fig 1: the signed measure nu -------------------------------------------------------------
rho = float(mp.findroot(lambda y: y**3 - y - 1, 1.3)); t0 = np.log(rho)
t = np.linspace(0.02, 3.0, 1500)
b = np.exp(-2.5*t)/(1-np.exp(-2*t)) - np.exp(t/2)
def mangoldt(n):
    for p in range(2, n+1):
        if n % p == 0:
            k = n
            while k % p == 0: k //= p
            return np.log(p) if k == 1 else 0.0
    return 0.0
ns = [n for n in range(2, 21) if mangoldt(n) > 0]
fig, ax = plt.subplots(figsize=(5.2, 3.0))
ax.plot(t, b, color="k", lw=1.2, label=r"$b(t)=\dfrac{e^{-5t/2}}{1-e^{-2t}}-e^{t/2}$")
ax.axhline(0, color="0.6", lw=0.6); ax.axvline(t0, color="0.4", ls="--", lw=0.8)
ax.text(t0+0.03, 1.2, r"$t_0=\log\rho=%.4f$" % t0, fontsize=8)
for n in ns:
    ax.vlines(np.log(n), 0, mangoldt(n)/np.sqrt(n), color="C3", lw=1.6)
ax.plot([], [], color="C3", lw=1.6, label=r"atoms $\Lambda(n)/\sqrt{n}$ at $t=\log n$")
ax.set_ylim(-1.0, 2.0); ax.set_xlim(0, 3.0); ax.set_xlabel(r"$t=|x-x'|$"); ax.set_ylabel(r"density / atom weight")
ax.legend(loc="upper right", frameon=False, fontsize=8); fig.tight_layout(); fig.savefig(OUT+"fig1_signed_measure.pdf"); plt.close(fig)

# ---- Fig 2: canonical test f0 and Xi ----------------------------------------------------------
h = lambda u: (mp.pi**2*u**4 - 1.5*mp.pi*u**2)*mp.e**(-mp.pi*u**2)
def Phi(x):
    x = abs(mp.mpf(x)); return 4*mp.e**(x/2)*mp.nsum(lambda n: h(n*mp.e**x), [1, mp.inf])
xs = np.linspace(-2.2, 2.2, 441); ph = np.array([float(Phi(x)) for x in xs])
A = float(mp.sqrt(mp.quad(lambda x: Phi(x)**2, [-6, -1, 0, 1, 6])))
xi = lambda s: (s-1)*mp.pi**(-s/2)*mp.gamma(s/2+1)*mp.zeta(s)
zs = np.linspace(0, 40, 801); Xi = np.array([float(mp.re(xi(mp.mpf(1)/2 + 1j*z))) for z in zs])
fig, (a1, a2) = plt.subplots(1, 2, figsize=(6.4, 2.6))
a1.plot(xs, ph/A, "k", lw=1.2); a1.set_xlabel(r"$x=\log u$"); a1.set_ylabel(r"$f_0(x)=\Phi(x)/\|\Phi\|_2$"); a1.set_title(r"canonical test, $\|\Phi\|_2=%.6f$" % A, fontsize=8)
a2.plot(zs, Xi/Xi[0], "k", lw=1.0); a2.axhline(0, color="0.6", lw=0.6); a2.set_xlabel(r"$z$"); a2.set_ylabel(r"$\Xi(z)/\Xi(0)$"); a2.set_title(r"$\widehat{f_0}=\Xi/\|\Phi\|_2$", fontsize=8)
a2.set_ylim(-0.02, 1.02)
fig.tight_layout(); fig.savefig(OUT+"fig2_canonical_test.pdf"); plt.close(fig)

# ---- Fig 3: window bottoms lambda_1(m,N) (arb-certified caches, Progress_Log 2026-09-04/05) ------
data = {13: [(13, None), (60, 1.0e-58), (120, 3.484e-59)],
        23: [(90, 1.9e-103), (110, 4.34e-109), (130, 8.2e-112), (145, 2.4e-112), (160, 1.8e-112)],
        43: [(43, 1.0e-90), (86, 2.2e-137), (130, 7.8e-170), (170, 1.4e-190), (215, 2.1e-206), (260, 5.8e-216), (300, 1.06e-219), (340, 2.62e-220), (380, 2.062e-220), (420, 1.871e-220), (460, 1.731e-220)]}
fig, ax = plt.subplots(figsize=(5.2, 3.0))
for m, pts in data.items():
    N = [p[0]/m for p in pts if p[1]]; L = [np.log10(p[1]) for p in pts if p[1]]
    ax.plot(N, L, "o-", ms=3.5, lw=1, label=r"$m=\lambda^2=%d$" % m)
ax.set_xlabel(r"$N/m$ (window width in modes)"); ax.set_ylabel(r"$\log_{10}\lambda_1(m,N)$")
ax.legend(frameon=False, fontsize=8); ax.set_title("bottom of the window form saturates at $N^*\\approx 4.6m,\\ 6.3m,\\ 8m$", fontsize=8)
fig.tight_layout(); fig.savefig(OUT+"fig3_window_bottoms.pdf"); plt.close(fig)

# ---- Fig 4: trial second jet constant a_m m -> 1/(16 pi) --------------------------------------
ms = np.array([13, 23, 43, 83]); am = np.array([0.020307, 0.020123, 0.020016, 0.0199568])
fig, ax = plt.subplots(figsize=(4.6, 2.8))
ax.plot(1/ms, am, "ko", ms=4, label=r"measured $a_m$")
xx = np.linspace(0, 0.08, 50); ax.plot(xx, 1/(16*np.pi) + 13/(256*np.pi**2)*xx, "k--", lw=0.9, label=r"$\frac{1}{16\pi}+\frac{13}{256\pi^2 m}$")
ax.set_xlabel(r"$1/m$"); ax.set_ylabel(r"$a_m=m\,(\kappa_\Xi-\kappa(k_\lambda))$"); ax.legend(frameon=False, fontsize=8)
fig.tight_layout(); fig.savefig(OUT+"fig4_trial_jet.pdf"); plt.close(fig)
print("A=", A, "t0=", t0, "rho=", rho, "13/(256pi^2)=", 13/(256*np.pi**2), "1/(16pi)=", 1/(16*np.pi))
