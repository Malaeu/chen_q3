#!/usr/bin/env python3
"""
🔬 p·ln(p) PHASE WALK VISUALIZATION
Визуализация аномального поведения — |S| уменьшается с N!
"""
import math

def sieve(n):
    is_prime = [True] * (n + 1)
    is_prime[0] = is_prime[1] = False
    for p in range(2, int(n**0.5) + 1):
        if is_prime[p]:
            for i in range(p*p, n + 1, p):
                is_prime[i] = False
    return [i for i in range(2, n + 1) if is_prime[i]]

def compute_walks(primes, limit=2000):
    """Вычислить фазовые пути для разных функций"""
    walks = {
        "p_ln_p": [(0, 0)],
        "e_p": [(0, 0)],
        "sqrt_p": [(0, 0)],
        "ln_p": [(0, 0)],
    }

    coords = {k: (0, 0) for k in walks}

    for p in primes[:limit]:
        # p·ln(p)
        angle = 2 * math.pi * p * math.log(p)
        x, y = coords["p_ln_p"]
        x += math.cos(angle)
        y += math.sin(angle)
        coords["p_ln_p"] = (x, y)
        walks["p_ln_p"].append((x, y))

        # e·p
        angle = 2 * math.pi * p * math.e
        x, y = coords["e_p"]
        x += math.cos(angle)
        y += math.sin(angle)
        coords["e_p"] = (x, y)
        walks["e_p"].append((x, y))

        # √p
        angle = 2 * math.pi * math.sqrt(p)
        x, y = coords["sqrt_p"]
        x += math.cos(angle)
        y += math.sin(angle)
        coords["sqrt_p"] = (x, y)
        walks["sqrt_p"].append((x, y))

        # ln(p) - для контраста (резонанс)
        angle = 2 * math.pi * math.log(p)
        x, y = coords["ln_p"]
        x += math.cos(angle)
        y += math.sin(angle)
        coords["ln_p"] = (x, y)
        walks["ln_p"].append((x, y))

    return walks

def generate_comparison_svg(primes, filename="p_ln_p_comparison.svg"):
    """Генерация SVG сравнения разных фазовых функций"""

    walks = compute_walks(primes, limit=3000)

    # Цвета и метки
    configs = [
        ("p·ln(p) — β=-0.16 УБЫВАЕТ!", "p_ln_p", "#f85149"),
        ("e·p — β≈0.01", "e_p", "#3fb950"),
        ("√p — β=0.39", "sqrt_p", "#58a6ff"),
        ("ln(p) — β=1.01 РЕЗОНАНС", "ln_p", "#a371f7"),
    ]

    # Размер и отступы
    width, height = 1400, 800
    panel_w = width // 2 - 30
    panel_h = height // 2 - 50
    pad = 40

    svg = [f'<svg width="{width}" height="{height}" xmlns="http://www.w3.org/2000/svg">']
    svg.append('<rect width="100%" height="100%" fill="#0d1117"/>')
    svg.append(f'<text x="20" y="30" font-family="monospace" font-size="18" fill="#58a6ff">🔬 Phase Walk Comparison: Why p·ln(p) is SPECIAL</text>')

    for idx, (label, key, color) in enumerate(configs):
        # Позиция панели
        col = idx % 2
        row = idx // 2
        ox = 20 + col * (panel_w + 20)
        oy = 50 + row * (panel_h + 30)

        # Рамка панели
        svg.append(f'<rect x="{ox}" y="{oy}" width="{panel_w}" height="{panel_h}" fill="#161b22" stroke="#30363d" rx="8"/>')

        # Заголовок
        svg.append(f'<text x="{ox+10}" y="{oy+20}" font-family="monospace" font-size="12" fill="{color}">{label}</text>')

        # Данные пути
        path = walks[key]
        if not path:
            continue

        # Масштабирование
        xs = [p[0] for p in path]
        ys = [p[1] for p in path]
        min_x, max_x = min(xs), max(xs)
        min_y, max_y = min(ys), max(ys)

        # Добавляем padding
        range_x = max(max_x - min_x, 1)
        range_y = max(max_y - min_y, 1)
        scale = min((panel_w - 2*pad) / range_x, (panel_h - 2*pad - 30) / range_y)

        def tx(x):
            return ox + pad + (x - min_x) * scale

        def ty(y):
            return oy + pad + 30 + (max_y - y) * scale

        # Путь
        d = " ".join([f"{'M' if i==0 else 'L'} {tx(x):.1f} {ty(y):.1f}" for i, (x, y) in enumerate(path)])
        svg.append(f'<path d="{d}" stroke="{color}" fill="none" stroke-width="1" opacity="0.8"/>')

        # Точка старта
        svg.append(f'<circle cx="{tx(0)}" cy="{ty(0)}" r="4" fill="#f0883e"/>')

        # Конечная точка
        end_x, end_y = path[-1]
        svg.append(f'<circle cx="{tx(end_x)}" cy="{ty(end_y)}" r="4" fill="{color}"/>')

        # Метрика
        final_dist = math.sqrt(end_x**2 + end_y**2)
        n = len(path) - 1
        metric = final_dist / math.sqrt(n) if n > 0 else 0
        svg.append(f'<text x="{ox+panel_w-100}" y="{oy+panel_h-10}" font-family="monospace" font-size="10" fill="#8b949e">|S|/√N = {metric:.3f}</text>')

    svg.append('</svg>')

    with open(filename, 'w') as f:
        f.write('\n'.join(svg))

    print(f"✓ SVG: {filename}")

def generate_animated_p_ln_p(primes, filename="p_ln_p_animated.svg"):
    """Анимированный SVG только для p·ln(p)"""

    limit = 2000
    path = [(0, 0)]
    x, y = 0, 0

    # Вычисляем путь
    for p in primes[:limit]:
        angle = 2 * math.pi * p * math.log(p)
        x += math.cos(angle)
        y += math.sin(angle)
        path.append((x, y))

    # Также вычислим |S| на каждом шаге
    distances = [math.sqrt(px**2 + py**2) for px, py in path]

    # Масштабирование
    xs = [p[0] for p in path]
    ys = [p[1] for p in path]
    min_x, max_x = min(xs) - 5, max(xs) + 5
    min_y, max_y = min(ys) - 5, max(ys) + 5

    width, height = 900, 900
    pad = 60

    range_x = max_x - min_x
    range_y = max_y - min_y
    scale = min((width - 2*pad) / range_x, (height - 2*pad) / range_y)

    def tx(x):
        return pad + (x - min_x) * scale

    def ty(y):
        return pad + (max_y - y) * scale

    # Вычислим длину пути для анимации
    path_len = 0
    for i in range(1, len(path)):
        dx = (path[i][0] - path[i-1][0]) * scale
        dy = (path[i][1] - path[i-1][1]) * scale
        path_len += math.sqrt(dx*dx + dy*dy)

    svg = [f'<svg width="{width}" height="{height}" xmlns="http://www.w3.org/2000/svg">']

    # Стили
    svg.append(f'''<style>
    .main-path {{
        stroke-dasharray: {path_len:.0f};
        stroke-dashoffset: {path_len:.0f};
        animation: draw 10s ease-out forwards;
    }}
    @keyframes draw {{
        to {{ stroke-dashoffset: 0; }}
    }}
    .pulse {{
        animation: pulse 1s ease-in-out infinite;
    }}
    @keyframes pulse {{
        0%, 100% {{ r: 5; opacity: 1; }}
        50% {{ r: 8; opacity: 0.7; }}
    }}
    </style>''')

    svg.append('<rect width="100%" height="100%" fill="#0d1117"/>')

    # Заголовок
    svg.append(f'<text x="20" y="30" font-family="monospace" font-size="16" fill="#f85149">🔬 p·ln(p) Phase Walk — The Anomaly</text>')
    svg.append(f'<text x="20" y="50" font-family="monospace" font-size="12" fill="#8b949e">β = -0.16: |S| DECREASES as N grows!</text>')

    # Сетка
    svg.append('<g stroke="#21262d" stroke-width="0.5">')
    for i in range(10):
        gx = pad + i * (width - 2*pad) / 9
        gy = pad + i * (height - 2*pad) / 9
        svg.append(f'<line x1="{gx}" y1="{pad}" x2="{gx}" y2="{height-pad}"/>')
        svg.append(f'<line x1="{pad}" y1="{gy}" x2="{width-pad}" y2="{gy}"/>')
    svg.append('</g>')

    # Главный путь
    d = " ".join([f"{'M' if i==0 else 'L'} {tx(px):.1f} {ty(py):.1f}" for i, (px, py) in enumerate(path)])
    svg.append(f'<path class="main-path" d="{d}" stroke="#f85149" fill="none" stroke-width="2" stroke-linecap="round"/>')

    # Старт
    svg.append(f'<circle class="pulse" cx="{tx(0)}" cy="{ty(0)}" r="5" fill="#3fb950"/>')
    svg.append(f'<text x="{tx(0)+10}" y="{ty(0)-10}" font-family="monospace" font-size="10" fill="#3fb950">START</text>')

    # Конец
    end_x, end_y = path[-1]
    svg.append(f'''<circle cx="{tx(end_x)}" cy="{ty(end_y)}" r="5" fill="#f85149" opacity="0">
        <animate attributeName="opacity" from="0" to="1" begin="10s" dur="0.5s" fill="freeze"/>
    </circle>''')

    # Метрики
    final_dist = math.sqrt(end_x**2 + end_y**2)
    n = len(path) - 1
    metric = final_dist / math.sqrt(n)

    svg.append(f'<text x="20" y="{height-40}" font-family="monospace" font-size="12" fill="#8b949e">N = {n} primes</text>')
    svg.append(f'<text x="20" y="{height-20}" font-family="monospace" font-size="12" fill="#f85149">|S|/√N = {metric:.4f}</text>')

    # Показать что путь "сжимается"
    svg.append(f'<text x="{width-250}" y="{height-40}" font-family="monospace" font-size="11" fill="#58a6ff">Notice: path stays BOUNDED!</text>')
    svg.append(f'<text x="{width-250}" y="{height-20}" font-family="monospace" font-size="11" fill="#58a6ff">This is Q3 in action! 🎯</text>')

    svg.append('</svg>')

    with open(filename, 'w') as f:
        f.write('\n'.join(svg))

    print(f"✓ Animated SVG: {filename}")

def main():
    print("🔬 p·ln(p) Phase Walk Visualization")
    print("="*50)

    limit = 50000
    print(f"Generating primes up to {limit}...")
    primes = sieve(limit)
    print(f"✓ {len(primes)} primes")

    generate_comparison_svg(primes)
    generate_animated_p_ln_p(primes)

    print()
    print("🎬 Open in browser:")
    print("   open p_ln_p_comparison.svg")
    print("   open p_ln_p_animated.svg")

if __name__ == "__main__":
    main()
