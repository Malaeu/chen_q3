"""Predicted Fourier tail of P_m h: eps0 = sqrt(sum_{|n|>m} |c_n|^2), c_n = L^{-1/2} 4 Xi(2 pi n / L).
Compare with the measured ||K_m P_m h|| / ||P_m h|| (quasimode_norm_probe_dps50.txt). DIAGNOSTIC_NEVER_A_PROOF."""
import mpmath as mp
mp.mp.dps = 30
def Xi(t):
    s = mp.mpf(1) / 2 + 1j * t
    return mp.re(s * (s - 1) / 2 * mp.pi**(-s / 2) * mp.gamma(s / 2) * mp.zeta(s))
obs = {8: 4.4859e-7, 12: 6.3503e-10, 16: 1.1878e-10, 20: 1.7273e-12}
for m in (8, 12, 16, 20, 24):
    L = mp.log(m)
    eps0 = mp.sqrt(2 * sum((4 * Xi(2 * mp.pi * n / L))**2 / L for n in range(m + 1, 6 * m)))
    o = obs.get(m)
    print(f"m={m} t_m={mp.nstr(2*mp.pi*m/L,5)} eps0_pred={mp.nstr(eps0,4)} measured={o} ratio={mp.nstr(o/eps0,4) if o else '-'}")
