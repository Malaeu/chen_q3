"""
Quick probe of B_{pq}(X) growth for fixed twin primes p,q.

Definition used (matching paper, t=1):
    xi_n   = log(n) / (2*pi)
    K_pr   = exp(-(xi_p - xi_r)^2 / (4*t))
    B_pq   = sum_{r<=X} (xi_p - xi_r)*(xi_q - xi_r) * K_pr * K_qr

We compute B_pq(X) for a grid of X values and report a log-log slope.

Run:
    python -m src.bpq_growth --p 3 --q 5 --xmax 300000 --num 6

Dependencies: none beyond stdlib math; uses a simple sieve for primes.
"""
import argparse
import math
from typing import List, Tuple


def sieve_primes(n: int) -> List[int]:
    """Return all primes <= n using simple sieve."""
    if n < 2:
        return []
    size = n + 1
    is_prime = bytearray(b"\x01") * size
    is_prime[0:2] = b"\x00\x00"
    for p in range(2, int(n ** 0.5) + 1):
        if is_prime[p]:
            step = p
            start = p * p
            is_prime[start:size:step] = b"\x00" * ((size - start - 1) // step + 1)
    return [i for i, flag in enumerate(is_prime) if flag]


def xi(n: int) -> float:
    return math.log(n) / (2 * math.pi)


def compute_Bpq(p: int, q: int, primes: List[int], t: float = 1.0) -> float:
    xi_p = xi(p)
    xi_q = xi(q)
    denom = 4 * t
    total = 0.0
    for r in primes:
        x = xi(r)
        kpr = math.exp(-((xi_p - x) ** 2) / denom)
        kqr = math.exp(-((xi_q - x) ** 2) / denom)
        total += (xi_p - x) * (xi_q - x) * kpr * kqr
    return total


def run(p: int, q: int, x_values: List[int], t: float) -> List[Tuple[int, float]]:
    out = []
    for X in x_values:
        primes = sieve_primes(X)
        b = compute_Bpq(p, q, primes, t=t)
        out.append((X, b))
    return out


def loglog_slope(data: List[Tuple[int, float]]) -> float:
    # least squares on (log X, log B)
    xs = [math.log(x) for x, _ in data]
    ys = [math.log(max(b, 1e-20)) for _, b in data]
    n = len(xs)
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    num = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    den = sum((x - mean_x) ** 2 for x in xs)
    return num / den if den > 0 else float("nan")


def main() -> None:
    parser = argparse.ArgumentParser(description="Grow B_pq(X) for fixed p,q.")
    parser.add_argument("--p", type=int, default=3, help="first twin prime")
    parser.add_argument("--q", type=int, default=5, help="second twin prime")
    parser.add_argument("--xmax", type=int, default=300000, help="max X")
    parser.add_argument("--num", type=int, default=6, help="number of X grid points")
    parser.add_argument("--t", type=float, default=1.0, help="Gaussian scale t")
    args = parser.parse_args()

    grid = sorted(set(int(args.xmax ** (i / (args.num - 1))) for i in range(args.num)))
    grid[0] = max(grid[0], args.q + 1)
    data = run(args.p, args.q, grid, args.t)

    slope = loglog_slope(data)
    print(f"p={args.p}, q={args.q}, t={args.t}")
    print("X\tB_pq")
    for X, b in data:
        print(f"{X}\t{b:.6e}")
    print(f"log-log slope ≈ {slope:.3f}")


if __name__ == "__main__":
    main()
