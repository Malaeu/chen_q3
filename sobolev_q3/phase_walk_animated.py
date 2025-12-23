#!/usr/bin/env python3
"""
Animated Phase Walk Visualization
Анимированная визуализация фазовых путей
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

def compute_phase_walk(numbers, alpha):
    """Фазовый путь для набора чисел."""
    path = [(0, 0)]
    x, y = 0, 0
    for n in numbers:
        x += math.cos(2 * math.pi * n * alpha)
        y += math.sin(2 * math.pi * n * alpha)
        path.append((x, y))
    return path

def generate_animated_svg(filename, paths, colors, labels, title, duration=10):
    """Анимированный SVG с CSS stroke-dasharray анимацией."""
    all_points = [p for path in paths for p in path]
    min_x = min(p[0] for p in all_points)
    max_x = max(p[0] for p in all_points)
    min_y = min(p[1] for p in all_points)
    max_y = max(p[1] for p in all_points)

    # Добавляем padding
    pad = 0.1 * max(max_x - min_x, max_y - min_y)
    min_x -= pad
    max_x += pad
    min_y -= pad
    max_y += pad

    width, height = 900, 900
    padding = 60

    def scale(val, min_v, max_v, size):
        if max_v == min_v:
            return size / 2
        return padding + (val - min_v) * (size - 2 * padding) / (max_v - min_v)

    # Вычисляем длину каждого пути для stroke-dasharray
    def path_length(path):
        total = 0
        for i in range(1, len(path)):
            dx = path[i][0] - path[i-1][0]
            dy = path[i][1] - path[i-1][1]
            total += math.sqrt(dx*dx + dy*dy)
        return total * (width / (max_x - min_x))  # масштабируем

    svg = [f'<svg width="{width}" height="{height}" xmlns="http://www.w3.org/2000/svg">']

    # CSS стили для анимации
    svg.append('<style>')
    for i, (path, color) in enumerate(zip(paths, colors)):
        plen = path_length(path) * 1.5  # с запасом
        delay = i * 0.5  # небольшая задержка между путями
        svg.append(f'''
    .path{i} {{
        stroke-dasharray: {plen:.0f};
        stroke-dashoffset: {plen:.0f};
        animation: draw{i} {duration}s ease-in-out {delay}s forwards;
    }}
    @keyframes draw{i} {{
        to {{ stroke-dashoffset: 0; }}
    }}
''')

    # Пульсирующая точка начала
    svg.append('''
    .start-point {
        animation: pulse 1s ease-in-out infinite;
    }
    @keyframes pulse {
        0%, 100% { r: 5; opacity: 1; }
        50% { r: 8; opacity: 0.7; }
    }

    .glow {
        filter: drop-shadow(0 0 3px currentColor);
    }
''')
    svg.append('</style>')

    # Фон
    svg.append(f'<rect width="100%" height="100%" fill="#0d1117"/>')

    # Заголовок
    svg.append(f'<text x="20" y="30" font-family="monospace" font-size="18" fill="#58a6ff">{title}</text>')

    # Легенда
    for i, (label, color) in enumerate(zip(labels, colors)):
        svg.append(f'<rect x="20" y="{55 + i*25}" width="30" height="3" fill="{color}" class="glow" style="color:{color}"/>')
        svg.append(f'<text x="60" y="{60 + i*25}" font-family="monospace" font-size="12" fill="#8b949e">{label}</text>')

    # Сетка (тонкая)
    svg.append('<g stroke="#21262d" stroke-width="0.5">')
    for i in range(10):
        x = padding + i * (width - 2*padding) / 9
        y = padding + i * (height - 2*padding) / 9
        svg.append(f'<line x1="{x}" y1="{padding}" x2="{x}" y2="{height-padding}"/>')
        svg.append(f'<line x1="{padding}" y1="{y}" x2="{width-padding}" y2="{y}"/>')
    svg.append('</g>')

    # Рисуем пути
    for i, (path, color) in enumerate(zip(paths, colors)):
        path_data = []
        for j, (x, y) in enumerate(path):
            sx = scale(x, min_x, max_x, width)
            sy = scale(y, min_y, max_y, height)
            path_data.append(f"{'M' if j == 0 else 'L'} {sx:.2f} {sy:.2f}")
        svg.append(f'<path class="path{i} glow" style="color:{color}" d="{" ".join(path_data)}" stroke="{color}" fill="none" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>')

    # Точка старта (анимированная)
    start_x = scale(0, min_x, max_x, width)
    start_y = scale(0, min_y, max_y, height)
    svg.append(f'<circle class="start-point" cx="{start_x}" cy="{start_y}" r="5" fill="#f85149"/>')

    # Метка "START"
    svg.append(f'<text x="{start_x + 10}" y="{start_y - 10}" font-family="monospace" font-size="10" fill="#f85149">START</text>')

    # Конечные точки
    for i, (path, color) in enumerate(zip(paths, colors)):
        end_x = scale(path[-1][0], min_x, max_x, width)
        end_y = scale(path[-1][1], min_y, max_y, height)
        svg.append(f'''
    <circle cx="{end_x}" cy="{end_y}" r="4" fill="{color}" opacity="0">
        <animate attributeName="opacity" from="0" to="1" begin="{duration + i*0.5}s" dur="0.5s" fill="freeze"/>
    </circle>
''')

    svg.append('</svg>')

    with open(filename, 'w') as f:
        f.write("\n".join(svg))
    print(f"✓ {filename}")

# --- MAIN ---
if __name__ == "__main__":
    limit = 5000  # меньше для более плавной анимации
    primes = get_primes(limit)
    twins = get_twin_primes(primes)

    print(f"🔢 Primes до {limit}: {len(primes)}")
    print(f"👯 Twin primes: {len(twins)}")
    print()

    # MAJOR ARC: Резонанс - анимация
    alpha_major = 0.02
    path_all = compute_phase_walk(primes, alpha_major)
    path_twins = compute_phase_walk(twins, alpha_major)

    generate_animated_svg(
        "phase_walk_animated.svg",
        [path_all, path_twins],
        ["#39d353", "#f85149"],  # GitHub green, red
        [f"All primes ({len(primes)})", f"Twin primes ({len(twins)})"],
        "🎬 PHASE WALK ANIMATION (α=0.02)",
        duration=8
    )

    # Только близнецы - более детальная анимация
    generate_animated_svg(
        "twins_only_animated.svg",
        [path_twins],
        ["#f85149"],
        [f"Twin primes ({len(twins)})"],
        "🔴 TWIN PRIMES RESONANCE",
        duration=6
    )

    # Minor arc для сравнения
    alpha_minor = math.sqrt(2)
    path_all_minor = compute_phase_walk(primes[:500], alpha_minor)  # меньше точек
    path_twins_minor = compute_phase_walk(twins[:200], alpha_minor)

    generate_animated_svg(
        "minor_arc_animated.svg",
        [path_all_minor, path_twins_minor],
        ["#39d353", "#f85149"],
        ["All primes (500)", "Twin primes (200)"],
        "🌀 MINOR ARC: Chaos (α=√2)",
        duration=6
    )

    print()
    print("🎬 Анимации готовы! Открывай в браузере:")
    print("   open phase_walk_animated.svg")
    print("   open twins_only_animated.svg")
    print("   open minor_arc_animated.svg")
