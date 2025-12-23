#!/usr/bin/env python3
"""
🔬 TWIN PRIMES MOD 6 STRUCTURE
Визуализация почему все близнецы имеют вид (6k-1, 6k+1)
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

def get_twins(primes):
    prime_set = set(primes)
    return [(p, p+2) for p in primes if p+2 in prime_set]

def generate_mod6_viz(primes, twins, filename="twins_mod6_structure.svg"):
    """Визуализация mod 6 структуры близнецов"""

    width, height = 1200, 900

    svg = [f'<svg width="{width}" height="{height}" xmlns="http://www.w3.org/2000/svg">']
    svg.append('<rect width="100%" height="100%" fill="#0d1117"/>')

    # Заголовок
    svg.append(f'<text x="20" y="35" font-family="monospace" font-size="22" fill="#58a6ff">🔬 Twin Primes mod 6 Structure</text>')
    svg.append(f'<text x="20" y="58" font-family="monospace" font-size="12" fill="#8b949e">Why ALL twins (except 3,5) have form (6k-1, 6k+1)?</text>')

    # ═══════════════════════════════════════════════════════════════
    # СЕКЦИЯ 1: Почему простые = 6k±1
    # ═══════════════════════════════════════════════════════════════
    y_offset = 90
    svg.append(f'<text x="30" y="{y_offset}" font-family="monospace" font-size="14" fill="#ffa657" font-weight="bold">1️⃣ WHY primes &gt; 3 are 6k±1:</text>')

    y_offset += 25
    residues = [
        ("6k", "÷6", "#f85149", "✗"),
        ("6k+1", "prime?", "#3fb950", "✓"),
        ("6k+2", "÷2", "#f85149", "✗"),
        ("6k+3", "÷3", "#f85149", "✗"),
        ("6k+4", "÷2", "#f85149", "✗"),
        ("6k+5", "=6k-1, prime?", "#3fb950", "✓"),
    ]

    for i, (form, reason, color, mark) in enumerate(residues):
        x = 50 + (i % 3) * 200
        y = y_offset + (i // 3) * 35
        svg.append(f'<rect x="{x}" y="{y}" width="180" height="28" fill="#161b22" stroke="{color}" rx="4"/>')
        svg.append(f'<text x="{x+10}" y="{y+19}" font-family="monospace" font-size="12" fill="{color}">{form} → {reason} {mark}</text>')

    # ═══════════════════════════════════════════════════════════════
    # СЕКЦИЯ 2: Почему близнецы = (6k-1, 6k+1)
    # ═══════════════════════════════════════════════════════════════
    y_offset += 100
    svg.append(f'<text x="30" y="{y_offset}" font-family="monospace" font-size="14" fill="#ffa657" font-weight="bold">2️⃣ WHY twins must be (6k-1, 6k+1):</text>')

    y_offset += 30
    cases = [
        ("p = 6k-1", "p+2 = 6k+1", "Both can be prime!", "#3fb950", "✓ TWINS!"),
        ("p = 6k+1", "p+2 = 6k+3 = 3(2k+1)", "Divisible by 3!", "#f85149", "✗ IMPOSSIBLE"),
    ]

    for i, (p_form, p2_form, reason, color, result) in enumerate(cases):
        y = y_offset + i * 50
        svg.append(f'<rect x="50" y="{y}" width="500" height="40" fill="#161b22" stroke="{color}" rx="6"/>')
        svg.append(f'<text x="65" y="{y+17}" font-family="monospace" font-size="11" fill="#8b949e">{p_form} → {p2_form}</text>')
        svg.append(f'<text x="65" y="{y+32}" font-family="monospace" font-size="11" fill="{color}">{reason} {result}</text>')

    # ═══════════════════════════════════════════════════════════════
    # СЕКЦИЯ 3: Статистика mod 6
    # ═══════════════════════════════════════════════════════════════
    y_offset += 130
    svg.append(f'<text x="30" y="{y_offset}" font-family="monospace" font-size="14" fill="#ffa657" font-weight="bold">3️⃣ STATISTICS: Distribution of p (from twins) mod 6:</text>')

    # Считаем статистику
    mod6_stats = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0}
    for p, q in twins:
        mod6_stats[p % 6] += 1

    total = sum(mod6_stats.values())
    max_count = max(mod6_stats.values()) if mod6_stats.values() else 1

    y_offset += 20
    bar_width = 400

    for k in range(6):
        y = y_offset + k * 30
        count = mod6_stats[k]
        pct = count / total * 100 if total > 0 else 0
        bar_len = count / max_count * bar_width if max_count > 0 else 0

        # Цвет: зелёный для 5 (=6k-1), серый для остальных
        if k == 5:
            color = "#3fb950"
            label_extra = " ← ALL TWINS HERE!"
        elif k == 1:
            color = "#8b949e"
            label_extra = " (only (3,5))"
        else:
            color = "#30363d"
            label_extra = ""

        svg.append(f'<text x="50" y="{y+15}" font-family="monospace" font-size="11" fill="#8b949e">p ≡ {k} (mod 6):</text>')
        svg.append(f'<rect x="160" y="{y+2}" width="{bar_len}" height="18" fill="{color}" rx="2"/>')
        svg.append(f'<text x="{170 + bar_len}" y="{y+15}" font-family="monospace" font-size="11" fill="{color}">{count} ({pct:.1f}%){label_extra}</text>')

    # ═══════════════════════════════════════════════════════════════
    # СЕКЦИЯ 4: Решётка 6k±1
    # ═══════════════════════════════════════════════════════════════
    y_offset += 210
    svg.append(f'<text x="30" y="{y_offset}" font-family="monospace" font-size="14" fill="#ffa657" font-weight="bold">4️⃣ THE 6k±1 LATTICE (first 100 numbers):</text>')

    y_offset += 15
    grid_x, grid_y = 50, y_offset
    cell_w, cell_h = 22, 22
    cols = 20

    prime_set = set(primes)
    twin_set = set()
    for p, q in twins:
        twin_set.add(p)
        twin_set.add(q)

    for n in range(1, 101):
        col = (n - 1) % cols
        row = (n - 1) // cols
        x = grid_x + col * cell_w
        y = grid_y + row * cell_h

        mod6 = n % 6

        # Цвет фона
        if n in twin_set:
            bg_color = "#3fb950"  # twin prime = зелёный
            text_color = "#0d1117"
        elif n in prime_set:
            bg_color = "#58a6ff"  # prime = синий
            text_color = "#0d1117"
        elif mod6 == 1 or mod6 == 5:
            bg_color = "#21262d"  # 6k±1 но не prime
            text_color = "#8b949e"
        else:
            bg_color = "#161b22"  # не 6k±1
            text_color = "#30363d"

        svg.append(f'<rect x="{x}" y="{y}" width="{cell_w-2}" height="{cell_h-2}" fill="{bg_color}" rx="2"/>')
        svg.append(f'<text x="{x+cell_w//2-1}" y="{y+cell_h//2+3}" font-family="monospace" font-size="8" fill="{text_color}" text-anchor="middle">{n}</text>')

    # Легенда для решётки
    legend_y = y_offset + 5 * cell_h + 15
    legends = [
        ("#3fb950", "Twin prime"),
        ("#58a6ff", "Prime (not twin)"),
        ("#21262d", "6k±1 (composite)"),
        ("#161b22", "Not 6k±1"),
    ]
    for i, (color, label) in enumerate(legends):
        x = 50 + i * 160
        svg.append(f'<rect x="{x}" y="{legend_y}" width="12" height="12" fill="{color}" rx="2"/>')
        svg.append(f'<text x="{x+18}" y="{legend_y+10}" font-family="monospace" font-size="10" fill="#8b949e">{label}</text>')

    # ═══════════════════════════════════════════════════════════════
    # СЕКЦИЯ 5: Связь с ln(2) и ln(3)
    # ═══════════════════════════════════════════════════════════════
    info_x = 620
    info_y = 90

    svg.append(f'<rect x="{info_x}" y="{info_y}" width="550" height="280" fill="#161b22" stroke="#30363d" rx="8"/>')
    svg.append(f'<text x="{info_x+15}" y="{info_y+25}" font-family="monospace" font-size="14" fill="#a371f7" font-weight="bold">🎯 CONNECTION TO ln(2) AND ln(3):</text>')

    lines = [
        "",
        "6 = 2 × 3",
        "",
        "ln(2) ← encodes the difference (p+2 - p = 2)",
        "ln(3) ← encodes the mod 3 structure",
        "",
        "Together they capture the FULL mod 6 lattice!",
        "",
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━",
        "",
        "Phase function f(p) = p·ln(3):",
        "",
        "  For twins (6k-1, 6k+1):",
        "    f(6k-1) = (6k-1)·ln(3)",
        "    f(6k+1) = (6k+1)·ln(3)",
        "    Δf = 2·ln(3) = ln(9)",
        "",
        "  Phase shift: Δφ = 2π·ln(9) ≈ 13.8 rad",
        "              ≈ 72° (mod 360°) = 360°/5",
        "",
        "  → 5-fold symmetry → CANCELLATION!",
    ]

    for i, line in enumerate(lines):
        y = info_y + 45 + i * 11
        color = "#ffa657" if "ln(2)" in line or "ln(3)" in line or "ln(9)" in line else "#8b949e"
        if "CANCELLATION" in line:
            color = "#3fb950"
        svg.append(f'<text x="{info_x+20}" y="{y}" font-family="monospace" font-size="10" fill="{color}">{line}</text>')

    # Финальный вывод
    svg.append(f'<rect x="{info_x}" y="{info_y+300}" width="550" height="60" fill="#1a3d1a" stroke="#3fb950" rx="8"/>')
    svg.append(f'<text x="{info_x+15}" y="{info_y+325}" font-family="monospace" font-size="12" fill="#3fb950" font-weight="bold">✨ CONCLUSION:</text>')
    svg.append(f'<text x="{info_x+15}" y="{info_y+345}" font-family="monospace" font-size="11" fill="#8b949e">Twins live on 6k±1 lattice → ln(2), ln(3) are natural frequencies!</text>')

    svg.append('</svg>')

    with open(filename, 'w') as f:
        f.write('\n'.join(svg))

    print(f"✓ SVG: {filename}")

def print_stats(twins):
    """Печать статистики"""
    print("\n📊 Twin primes mod 6 distribution:")
    print("-" * 40)

    mod6_stats = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0}
    for p, q in twins:
        mod6_stats[p % 6] += 1

    total = sum(mod6_stats.values())

    for k in range(6):
        count = mod6_stats[k]
        pct = count / total * 100 if total > 0 else 0
        bar = "█" * (count // 20)
        note = " ← ALL TWINS!" if k == 5 else (" (3,5 only)" if k == 1 and count == 1 else "")
        print(f"  p ≡ {k} (mod 6): {count:5d} ({pct:5.1f}%) {bar}{note}")

def main():
    print("🔬 Twin Primes mod 6 Structure")
    print("="*50)

    N = 100000
    print(f"Generating primes up to {N}...")
    primes = sieve(N)
    twins = get_twins(primes)
    print(f"✓ {len(primes)} primes, {len(twins)} twin pairs")

    print_stats(twins)

    print()
    generate_mod6_viz(primes, twins)

    print()
    print("🎬 Open: open twins_mod6_structure.svg")

if __name__ == "__main__":
    main()
