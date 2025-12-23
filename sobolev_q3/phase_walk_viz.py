#!/usr/bin/env python3
"""
Phase Walk Visualization for Prime Number Theory
Визуализация фазовых путей для теории простых чисел
"""
import math

def get_primes(n):
    """Решето Эратосфена."""
    primes = []
    sieve = [True] * (n + 1)
    for p in range(2, n + 1):
        if sieve[p]:
            primes.append(p)
            for i in range(p * p, n + 1, p):
                sieve[i] = False
    return primes

def get_twin_primes(primes):
    """Извлекаем близнецов (p, p+2)."""
    twins = []
    prime_set = set(primes)
    for p in primes:
        if p + 2 in prime_set:
            twins.append(p)
            twins.append(p + 2)
    return sorted(set(twins))

def generate_svg_overlay(filename, paths, colors, labels, title):
    """SVG с несколькими путями для сравнения."""
    all_points = [p for path in paths for p in path]
    min_x = min(p[0] for p in all_points)
    max_x = max(p[0] for p in all_points)
    min_y = min(p[1] for p in all_points)
    max_y = max(p[1] for p in all_points)

    width, height = 900, 900
    padding = 60

    def scale(val, min_v, max_v, size):
        if max_v == min_v: return size / 2
        return padding + (val - min_v) * (size - 2 * padding) / (max_v - min_v)

    svg = [f'<svg width="{width}" height="{height}" xmlns="http://www.w3.org/2000/svg">']
    svg.append(f'<rect width="100%" height="100%" fill="#1a1a2e"/>')
    svg.append(f'<text x="20" y="30" font-family="monospace" font-size="18" fill="#eee">{title}</text>')

    # Легенда
    for i, (label, color) in enumerate(zip(labels, colors)):
        svg.append(f'<rect x="20" y="{55 + i*25}" width="20" height="3" fill="{color}"/>')
        svg.append(f'<text x="50" y="{60 + i*25}" font-family="monospace" font-size="12" fill="#ccc">{label}</text>')

    # Рисуем пути
    for path, color in zip(paths, colors):
        path_data = []
        for i, (x, y) in enumerate(path):
            sx = scale(x, min_x, max_x, width)
            sy = scale(y, min_y, max_y, height)
            path_data.append(f"{'M' if i == 0 else 'L'} {sx:.2f} {sy:.2f}")
        svg.append(f'<path d="{" ".join(path_data)}" stroke="{color}" fill="none" stroke-width="1.5" opacity="0.85"/>')

    # Центр (начало координат)
    cx = scale(0, min_x, max_x, width)
    cy = scale(0, min_y, max_y, height)
    svg.append(f'<circle cx="{cx}" cy="{cy}" r="5" fill="#ff6b6b"/>')

    svg.append('</svg>')

    with open(filename, 'w') as f:
        f.write("\n".join(svg))
    print(f"✓ {filename}")

def compute_phase_walk(numbers, alpha):
    """Фазовый путь для набора чисел."""
    path = [(0, 0)]
    x, y = 0, 0
    for n in numbers:
        x += math.cos(2 * math.pi * n * alpha)
        y += math.sin(2 * math.pi * n * alpha)
        path.append((x, y))
    return path

# --- MAIN ---
if __name__ == "__main__":
    limit = 8000
    primes = get_primes(limit)
    twins = get_twin_primes(primes)

    print(f"🔢 Primes до {limit}: {len(primes)}")
    print(f"👯 Twin primes: {len(twins)}")
    print()

    # MAJOR ARC: Резонанс
    alpha_major = 0.02
    path_all_major = compute_phase_walk(primes, alpha_major)
    path_twins_major = compute_phase_walk(twins, alpha_major)

    generate_svg_overlay(
        "twins_vs_all_major.svg",
        [path_all_major, path_twins_major],
        ["#4ecdc4", "#ff6b6b"],
        ["All primes", "Twin primes only"],
        "MAJOR ARC (α=0.02): Twins follow the resonance"
    )

    # MINOR ARC: Хаос/подавление
    alpha_minor = math.sqrt(2)
    path_all_minor = compute_phase_walk(primes, alpha_minor)
    path_twins_minor = compute_phase_walk(twins, alpha_minor)

    generate_svg_overlay(
        "twins_vs_all_minor.svg",
        [path_all_minor, path_twins_minor],
        ["#4ecdc4", "#ff6b6b"],
        ["All primes", "Twin primes only"],
        "MINOR ARC (α=√2): Q3 spectral suppression"
    )

    # BONUS: Несколько alpha для сравнения
    alphas = [0.01, 0.02, 0.05, 1/6]
    paths = [compute_phase_walk(twins, a) for a in alphas]
    colors = ["#e74c3c", "#f39c12", "#2ecc71", "#9b59b6"]
    labels = [f"α={a:.4f}" for a in alphas]

    generate_svg_overlay(
        "twins_multi_alpha.svg",
        paths, colors, labels,
        "Twin Primes: Different resonance frequencies"
    )

    print()
    print("🎯 Готово! Открывай SVG в браузере:")
    print("   open twins_vs_all_major.svg")
    print("   open twins_vs_all_minor.svg")
    print("   open twins_multi_alpha.svg")
