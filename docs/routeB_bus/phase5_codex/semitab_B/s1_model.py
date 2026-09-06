"""S1: build the model, validate F_inf (involution, self-adjointness, prolate eigenvalues)."""
import sys, time
import numpy as np
from numpy.polynomial.legendre import leggauss
from lib import Grid, Fourier, EulerS, build_FS, LOG2

np.set_printoptions(precision=12, suppress=False)


def slepian_even(c, ngl=400, nev=14):
    """independent computation: eigenvalues lambda_n(c) of the sinc kernel on [-1,1],
       Nystrom with Gauss-Legendre. Returns (all eigenvalues desc, parity flags)."""
    xs, ws = leggauss(ngl)
    D = xs[:, None] - xs[None, :]
    K = np.where(np.abs(D) < 1e-14, c / np.pi, np.sin(c * D) / (np.pi * D))
    A = np.sqrt(ws)[:, None] * K * np.sqrt(ws)[None, :]
    A = 0.5 * (A + A.T)
    w, V = np.linalg.eigh(A)
    idx = np.argsort(-w)
    w = w[idx][:nev]
    V = V[:, idx][:, :nev]
    # parity: eigenfunction psi(x) ~ V[:,n]/sqrt(w_i); compare with reversed nodes
    par = []
    for n in range(nev):
        v = V[:, n]
        par.append(1 if np.abs(v - v[::-1]).max() < np.abs(v + v[::-1]).max() else -1)
    return w, np.array(par)


def main(m=64, x_min=-38.0, x_max=5.0):
    t0 = time.time()
    g = Grid(m=m, x_min=x_min, x_max=x_max)
    print(g, flush=True)
    F = Fourier(g)
    print(f"[chi] max | |chi| - 1 | = {F.chi_abs_err:.3e}   (then normalised to exact modulus 1)")
    print(f"[chi] max |chi(-tau) - conj(chi(tau))| = "
          f"{np.max(np.abs(F.chi[(-np.arange(g.N)) % g.N] - np.conj(F.chi))):.3e}")

    Fm = F.matrix()
    print(f"[F] max |Im| discarded            = {np.max(np.abs(np.imag(F.apply(np.eye(g.N))))):.3e}")
    print(f"[F] ||F - F^T||_max               = {np.max(np.abs(Fm - Fm.T)):.3e}")
    E2 = Fm @ Fm - np.eye(g.N)
    print(f"[F] ||F^2 - I||_max               = {np.max(np.abs(E2)):.3e}")
    print(f"[F] ||F^2 - I||_2 (est)           = {np.linalg.norm(E2, 2) if g.N < 3000 else float('nan'):.3e}")

    # analytic fixed point: f(u)=e^{-pi u^2} -> v(x) = e^{x/2} e^{-pi e^{2x}}
    v = np.exp(g.x / 2.0 - np.pi * np.exp(2 * g.x)) * np.sqrt(g.d)
    Fv = np.real(F.apply(v))
    print(f"[F] Gaussian self-duality: ||F v - v|| / ||v|| = "
          f"{np.linalg.norm(Fv - v)/np.linalg.norm(v):.3e}   (||v||={np.linalg.norm(v):.6f})")

    # --- prolate check for F_inf at lambda = 1, sqrt2, 2
    for lam in (1.0, np.sqrt(2.0), 2.0):
        loglam = np.log(lam)
        idxP = g.idx_le(loglam)
        sub = Fm[np.ix_(idxP, idxP)]
        al = np.linalg.eigvalsh(0.5 * (sub + sub.T))
        order = np.argsort(-np.abs(al))
        al = al[order][:10]
        c = 2 * np.pi * lam * lam
        w, par = slepian_even(c, ngl=500, nev=20)
        lam_even = w[par == 1][:10]
        print(f"\n--- lambda={lam:.6f}  (c = 2 pi lambda^2 = {c:.6f}), dim ran P = {len(idxP)}")
        print("  n   alpha_n           alpha_n^2            lambda_n(c) [GL sinc]   rel.diff")
        for n in range(8):
            rd = abs(al[n]**2 - lam_even[n]) / max(lam_even[n], 1e-300)
            print(f"  {n}  {al[n]:+.12f}   {al[n]**2:.12e}   {lam_even[n]:.12e}   {rd:.2e}")
        np.save(f"alpha_arch_lam{lam:.4f}.npy", al)
    print(f"\n[time] {time.time()-t0:.1f}s")


if __name__ == "__main__":
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    xm = float(sys.argv[2]) if len(sys.argv) > 2 else -38.0
    xM = float(sys.argv[3]) if len(sys.argv) > 3 else 5.0
    main(m, xm, xM)
