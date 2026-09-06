import sys, time
import numpy as np
from numpy.polynomial.legendre import leggauss
from phys import PhysModel


def slepian_even(c, ngl=500, nev=20):
    xs, ws = leggauss(ngl)
    D = xs[:, None] - xs[None, :]
    with np.errstate(invalid='ignore', divide='ignore'):
        K = np.sin(c * D) / (np.pi * D)
    np.fill_diagonal(K, c / np.pi)
    A = np.sqrt(ws)[:, None] * K * np.sqrt(ws)[None, :]
    A = 0.5 * (A + A.T)
    w, V = np.linalg.eigh(A)
    idx = np.argsort(-w); w = w[idx][:nev]; V = V[:, idx][:, :nev]
    par = np.array([1 if np.abs(V[:, n] - V[::-1, n]).max() < np.abs(V[:, n] + V[::-1, n]).max()
                    else -1 for n in range(nev)])
    return w[par == 1]


def main(N=4096):
    t0 = time.time()
    M = PhysModel(N)
    print(f"PhysModel N={N}  delta={M.delta:.6g}  U_max={M.U:.4f}  dim={M.n}")
    F = M.Fmat()
    print(f"[F] ||F-F^T||_max = {np.max(np.abs(F-F.T)):.3e}")
    E = F @ F - np.eye(M.n)
    print(f"[F] ||F^2-I||_max = {np.max(np.abs(E)):.3e}   ||F^2-I||_2 = {np.linalg.norm(E,2):.3e}")
    # analytic fixed point f(u)=e^{-pi u^2}
    f = np.exp(-np.pi * M.u**2); c = np.sqrt(M.w) * f
    print(f"[F] Gaussian self-duality ||Fc-c||/||c|| = {np.linalg.norm(F@c-c)/np.linalg.norm(c):.3e}")
    # second analytic fixed point: u e^{-pi u^2} is ODD; use (1-2pi u^2)e^{-pi u^2}? check Hermite-2
    g = (1 - 4*np.pi*M.u**2) * np.exp(-np.pi*M.u**2)   # eigenvalue -1 of the cosine transform
    cg = np.sqrt(M.w)*g
    print(f"[F] Hermite-2 (eigenvalue -1) ||Fc+c||/||c|| = {np.linalg.norm(F@cg+cg)/np.linalg.norm(cg):.3e}")

    for lam in (1.0, np.sqrt(2.0), 2.0):
        idxP = np.where(M.u <= lam + 1e-12)[0]
        sub = F[np.ix_(idxP, idxP)]
        al = np.linalg.eigvalsh(0.5*(sub+sub.T))
        al = al[np.argsort(-np.abs(al))]
        c = 2*np.pi*lam*lam
        ref = slepian_even(c)
        print(f"\n--- lambda={lam:.6f}  c={c:.6f}  dim ran P = {len(idxP)}")
        print("  n   alpha_n            alpha_n^2             lambda_n(c) GL-sinc      rel.diff")
        for n in range(7):
            rd = abs(al[n]**2-ref[n])/max(ref[n],1e-300)
            print(f"  {n}  {al[n]:+.12f}    {al[n]**2:.12e}    {ref[n]:.12e}    {rd:.2e}")
    print(f"[time] {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 4096)
