"""DIAGNOSTIC NUMERICS ONLY — NEVER A PROOF, NEVER A LEAN INPUT.

R2 preflight probe (Goal 058, physical-energy front).

Checks the exact first-order coefficient identity for the windowed E_star
packet in the log coordinate x in [0, L], L = 2*log(lambda), u = exp(x)/lambda:

  (2*pi*i*n/L) * c_n
    = L^{-1/2} * G(0+)
      - L^{-1/2} * sqrt(lambda) * h(lambda-) * D_n
      + Ghat'_n

where
  c_n     = L^{-1/2} * int_0^L exp(-2*pi*i*n*x/L) G(x) dx,
  G(x)    = sqrt(u) * sum_{p>=1} h(p*u)   (finite: p < lambda^2 active),
  D_n     = sum_{p=1}^{m-1} p^{-1/2} * exp(2*pi*i*n*log(p)/L),  m = lambda^2,
  Ghat'_n = Fourier coefficient of the cell-wise a.e. derivative G'.

Consequences probed:
  * with edge value h(lambda-) != 0 the row n^2*|c_n|^2 stalls (not summable);
  * with edge value 0 the LEFT trace G(0+) alone still stalls the row.
"""
import argparse
import numpy as np


def run(m: int, edge: float, ns, pts: int):
    lam = np.sqrt(m)
    L = 2 * np.log(lam)

    def h(y):
        y = np.abs(y)
        return np.where(y <= lam, (1 - (y / lam) ** 2) + edge, 0.0)

    def hp(y):
        return np.where(np.abs(y) < lam, -2 * y / lam ** 2, 0.0)

    def G(x):
        u = np.exp(x) / lam
        tot = np.zeros_like(x)
        for p in range(1, m + 1):
            tot += h(p * u)
        return np.sqrt(u) * tot

    def Gp(x):
        u = np.exp(x) / lam
        tot = np.zeros_like(x)
        for p in range(1, m + 1):
            tot += p * u * hp(p * u)
        return 0.5 * G(x) + np.sqrt(u) * tot

    seams = sorted(L - np.log(p) for p in range(2, m) if 0 < L - np.log(p) < L)
    cells = [0.0] + seams + [L]

    def fourier(f, n):
        tot = 0.0 + 0.0j
        for a, b in zip(cells[:-1], cells[1:]):
            x = np.linspace(a + 1e-12, b - 1e-12, pts)
            tot += np.trapz(np.exp(-2j * np.pi * n * x / L) * f(x), x)
        return tot / np.sqrt(L)

    G0 = G(np.array([1e-9]))[0]

    def D(n):
        return sum(p ** -0.5 * np.exp(2j * np.pi * n * np.log(p) / L)
                   for p in range(1, m))

    print(f"m={m} lambda={lam:.4f} L={L:.6f} G(0+)={G0:.6f} edge={edge}")
    print(f"{'n':>5} {'|lhs|':>12} {'|rhs|':>12} {'|err|':>10} {'n^2|c_n|^2':>12}")
    for n in ns:
        cn = fourier(G, n)
        lhs = 2j * np.pi * n / L * cn
        rhs = (G0 / np.sqrt(L)
               - edge * np.sqrt(lam) * D(n) / np.sqrt(L)
               + fourier(Gp, n))
        print(f"{n:>5} {abs(lhs):>12.6f} {abs(rhs):>12.6f} "
              f"{abs(lhs - rhs):>10.2e} {n ** 2 * abs(cn) ** 2:>12.6f}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=9)
    ap.add_argument("--edge", type=float, default=0.3)
    ap.add_argument("--pts", type=int, default=4000)
    args = ap.parse_args()
    ns = [1, 2, 5, 10, 20, 50, 100, 200]
    run(args.m, args.edge, ns, args.pts)
    print("\n--- control: edge value 0 (left trace only) ---")
    run(args.m, 0.0, [1, 10, 50, 100, 200], args.pts)
