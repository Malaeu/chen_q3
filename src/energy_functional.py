import numpy as np
from typing import Sequence, Tuple


def load_zeros(path: str, limit: int | None = None) -> np.ndarray:
    """Load zeros (one per line) as float array; optionally truncate to `limit`."""
    arr = np.loadtxt(path, dtype=np.float64)
    if limit is not None:
        arr = arr[:limit]
    return arr


def sinc(x: np.ndarray) -> np.ndarray:
    """Normalized sinc: sin(x)/x with safe handling near zero."""
    out = np.ones_like(x)
    mask = np.abs(x) > 1e-12
    out[mask] = np.sin(x[mask]) / x[mask]
    return out


def diagonal(gamma: np.ndarray, T: float, alpha: float, sigma: float) -> float:
    g = gamma[gamma <= T]
    return float(np.exp(-sigma * sigma * (g - alpha) ** 2).sum())


def off_diagonal(gamma: np.ndarray, T: float, alpha: float, sigma: float, cutoff: float = 10.0) -> float:
    g = gamma[gamma <= T]
    n = g.size
    if n == 0:
        return 0.0
    # weights
    w = np.exp(-0.5 * sigma * sigma * (g - alpha) ** 2)
    # pairwise diffs with cutoff
    # We'll use a block approach to limit memory.
    cutoff_val = cutoff / sigma
    total = 0.0
    block = 4000  # tune for memory/speed
    for i in range(0, n, block):
        gi = g[i : i + block]
        wi = w[i : i + block]
        # diffs to all
        diff = gi[:, None] - g[None, :]
        mask = np.abs(diff) > 1e-12
        # apply cutoff
        cutoff_mask = np.abs(diff) <= cutoff_val
        valid = mask & cutoff_mask
        if not np.any(valid):
            continue
        wij = wi[:, None] * w[None, :]
        sinc_term = sinc(T * diff)
        contrib = wij * sinc_term
        total += contrib[valid].sum()
    return float(total)


def energy(gamma: np.ndarray, T: float, alpha: float, sigma: float, cutoff: float = 10.0) -> Tuple[float, float, float]:
    d = diagonal(gamma, T, alpha, sigma)
    o = off_diagonal(gamma, T, alpha, sigma, cutoff)
    return d, o, d + o


def off_diagonal_sample(
    gamma: np.ndarray,
    T: float,
    alpha: float,
    sigma: float,
    num_pairs: int,
    seed: int | None = None,
) -> Tuple[float, float]:
    """
    Monte Carlo estimate of the off-diagonal term.

    Returns (mean_estimate, stderr_estimate) where stderr is the sampling std error.
    """
    rng = np.random.default_rng(seed)
    n = gamma.size
    if n < 2:
        return 0.0, 0.0
    i = rng.integers(0, n, size=num_pairs, endpoint=False)
    j = rng.integers(0, n, size=num_pairs, endpoint=False)
    mask = i != j
    i, j = i[mask], j[mask]
    if i.size == 0:
        return 0.0, 0.0
    gi, gj = gamma[i], gamma[j]
    w = np.exp(-0.5 * sigma * sigma * ((gi - alpha) ** 2 + (gj - alpha) ** 2))
    diff = gi - gj
    contrib = w * sinc(T * diff)
    mean = float(contrib.mean())
    stderr = float(contrib.std(ddof=1) / np.sqrt(contrib.size))
    # scale up to full sum: N(N-1)
    scale = n * (n - 1)
    return mean * scale, stderr * scale


def compute_table(gamma: np.ndarray, Ts: Sequence[float], alpha: float, sigma: float, cutoff: float = 10.0) -> list[tuple[float, float, float, float]]:
    rows = []
    for T in Ts:
        d, o, e = energy(gamma, T, alpha, sigma, cutoff)
        rows.append((T, d, o, e))
    return rows


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Energy functional E(T)")
    parser.add_argument("--zeros", default="/Users/emalam/Documents/GitHub/RH_August_September_2025/zeros/zeros100k.txt")
    parser.add_argument("--limit", type=int, default=10000, help="number of zeros to use")
    parser.add_argument("--alpha", type=float, default=1.0)
    parser.add_argument("--sigma", type=float, default=1.0)
    parser.add_argument("--cutoff", type=float, default=10.0, help="|gamma_i-gamma_j| <= cutoff/sigma")
    parser.add_argument("--Ts", type=float, nargs="*", default=[100, 500, 1000, 5000, 10000, 50000])
    parser.add_argument("--out", default="/Users/emalam/Documents/GitHub/chen_q3/output/energy_table.txt")
    args = parser.parse_args()

    gamma = load_zeros(args.zeros, args.limit)
    rows = compute_table(gamma, args.Ts, args.alpha, args.sigma, args.cutoff)

    import os
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w") as f:
        f.write("T\tD\tO\tE\n")
        for T, d, o, e in rows:
            f.write(f"{T}\t{d:.12e}\t{o:.12e}\t{e:.12e}\n")

    # quick print
    for T, d, o, e in rows:
        print(f"T={T:>8}  D={d:.6e}  O={o:.6e}  E={e:.6e}")

    # plot
    try:
        import matplotlib.pyplot as plt
        Ts = [r[0] for r in rows]
        Ds = [r[1] for r in rows]
        Os = [abs(r[2]) for r in rows]
        Es = [r[3] for r in rows]
        plt.figure()
        plt.loglog(Ts, Ds, label="D(T)")
        plt.loglog(Ts, Os, label="|O(T)|")
        plt.loglog(Ts, Es, label="E(T)")
        plt.xlabel("T")
        plt.ylabel("value (log scale)")
        plt.legend()
        plt.tight_layout()
        plt.savefig("/Users/emalam/Documents/GitHub/chen_q3/output/energy_plot.png", dpi=200)
    except Exception as e:  # noqa: PIE786
        print("Plotting skipped:", e)


if __name__ == "__main__":
    main()
