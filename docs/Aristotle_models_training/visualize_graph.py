#!/usr/bin/env python3.11
"""
Визуализация графа зависимостей RH_Q3.pdf
"""

import json
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
from collections import defaultdict

# Загружаем данные
with open("/home/ubuntu/aristotle_research_package/rh_q3_analysis/dependency_graph.json") as f:
    data = json.load(f)

nodes = {n["id"]: n for n in data["nodes"]}
edges = data["edges"]

# Цвета по секциям
section_colors = {
    "5": "#E8F5E9",   # Светло-зелёный
    "6": "#E3F2FD",   # Светло-синий
    "7": "#FFF3E0",   # Светло-оранжевый
    "8": "#FCE4EC",   # Светло-розовый
    "9": "#F3E5F5",   # Светло-фиолетовый
    "10": "#FFEBEE",  # Светло-красный
    "11": "#E0F7FA", # Светло-бирюзовый
}

# Цвета границ по типу блокера
blocker_colors = {
    "none": "#4CAF50",   # Зелёный
    "soft": "#FF9800",   # Оранжевый
    "hard": "#F44336",   # Красный
}

# ============================================================================
# СОЗДАНИЕ ВИЗУАЛИЗАЦИИ
# ============================================================================

fig, axes = plt.subplots(1, 2, figsize=(20, 14))

# --- ЛЕВЫЙ ГРАФИК: TOP-20 по ERS ---
ax1 = axes[0]

# Сортируем по ERS
sorted_nodes = sorted(data["nodes"], key=lambda n: n["ers"], reverse=True)[:20]

y_pos = np.arange(len(sorted_nodes))
ers_values = [n["ers"] for n in sorted_nodes]
raw_values = [n["raw_risk"] for n in sorted_nodes]
inh_values = [n["inherited_risk"] for n in sorted_nodes]
cpb_values = [n["critical_path_bonus"] for n in sorted_nodes]

# Стековая диаграмма
bars1 = ax1.barh(y_pos, raw_values, color='#2196F3', label='Raw Risk')
bars2 = ax1.barh(y_pos, inh_values, left=raw_values, color='#FF9800', label='Inherited Risk')
bars3 = ax1.barh(y_pos, cpb_values, left=[r+i for r,i in zip(raw_values, inh_values)], 
                 color='#F44336', label='Critical Path Bonus')

# Метки
labels = [n["id"] for n in sorted_nodes]
ax1.set_yticks(y_pos)
ax1.set_yticklabels(labels, fontsize=9)
ax1.invert_yaxis()
ax1.set_xlabel('Effective Risk Score (ERS)', fontsize=12)
ax1.set_title('TOP-20 Nodes by ERS\n(Priority for Lean Formalization)', fontsize=14, fontweight='bold')
ax1.legend(loc='lower right')

# Добавляем значения ERS
for i, (bar, ers) in enumerate(zip(bars1, ers_values)):
    ax1.text(ers + 5, bar.get_y() + bar.get_height()/2, f'{ers:.1f}', 
             va='center', fontsize=8)

ax1.set_xlim(0, max(ers_values) * 1.15)
ax1.grid(axis='x', alpha=0.3)

# --- ПРАВЫЙ ГРАФИК: Статистика по секциям ---
ax2 = axes[1]

# Группируем по секциям
section_data = defaultdict(lambda: {"count": 0, "total_ers": 0, "nodes": []})
for n in data["nodes"]:
    section_data[n["section"]]["count"] += 1
    section_data[n["section"]]["total_ers"] += n["ers"]
    section_data[n["section"]]["nodes"].append(n)

sections = sorted(section_data.keys())
counts = [section_data[s]["count"] for s in sections]
total_ers = [section_data[s]["total_ers"] for s in sections]
avg_ers = [t/c if c > 0 else 0 for t, c in zip(total_ers, counts)]

x = np.arange(len(sections))
width = 0.35

bars1 = ax2.bar(x - width/2, counts, width, label='Node Count', color='#2196F3')
ax2_twin = ax2.twinx()
bars2 = ax2_twin.bar(x + width/2, avg_ers, width, label='Avg ERS', color='#FF5722')

ax2.set_xlabel('Section', fontsize=12)
ax2.set_ylabel('Node Count', fontsize=12, color='#2196F3')
ax2_twin.set_ylabel('Average ERS', fontsize=12, color='#FF5722')
ax2.set_xticks(x)
ax2.set_xticklabels([f'§{s}' for s in sections])
ax2.set_title('Distribution by Section', fontsize=14, fontweight='bold')

# Легенда
lines1, labels1 = ax2.get_legend_handles_labels()
lines2, labels2 = ax2_twin.get_legend_handles_labels()
ax2.legend(lines1 + lines2, labels1 + labels2, loc='upper right')

# Добавляем значения
for bar, count in zip(bars1, counts):
    ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.5, 
             str(count), ha='center', fontsize=9)

for bar, avg in zip(bars2, avg_ers):
    ax2_twin.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 2, 
                  f'{avg:.0f}', ha='center', fontsize=9)

plt.tight_layout()
plt.savefig('/home/ubuntu/aristotle_research_package/rh_q3_analysis/ers_analysis.png', dpi=150, bbox_inches='tight')
print("Saved: ers_analysis.png")

# ============================================================================
# СОЗДАНИЕ ДИАГРАММЫ КРИТИЧЕСКОГО ПУТИ
# ============================================================================

fig2, ax3 = plt.subplots(figsize=(16, 10))

# Критический путь к thm_11_2
critical_path = ["thm_11_2", "thm_11_4", "thm_8_35", "lemma_8_19", "lemma_8_14", 
                 "lemma_8_12"]

# Позиции узлов по глубине
depth_positions = defaultdict(list)
for n in data["nodes"]:
    depth_positions[n["depth"]].append(n)

# Сортируем внутри каждой глубины по ERS
for depth in depth_positions:
    depth_positions[depth].sort(key=lambda x: x["ers"], reverse=True)

# Вычисляем позиции
node_positions = {}
max_depth = max(depth_positions.keys())

for depth, nodes_at_depth in depth_positions.items():
    n_nodes = len(nodes_at_depth)
    for i, node in enumerate(nodes_at_depth):
        x = depth
        y = (i - n_nodes/2) * 0.8
        node_positions[node["id"]] = (x, y)

# Рисуем рёбра
for edge in edges:
    if edge["source"] in node_positions and edge["target"] in node_positions:
        x1, y1 = node_positions[edge["source"]]
        x2, y2 = node_positions[edge["target"]]
        
        # Проверяем, на критическом пути ли
        is_critical = (edge["source"] in critical_path and edge["target"] in critical_path)
        
        color = '#F44336' if is_critical else '#BDBDBD'
        width = 2.5 if is_critical else 0.5
        alpha = 1.0 if is_critical else 0.3
        
        ax3.annotate("", xy=(x2, y2), xytext=(x1, y1),
                    arrowprops=dict(arrowstyle="->", color=color, lw=width, alpha=alpha))

# Рисуем узлы
for node_id, (x, y) in node_positions.items():
    node = nodes[node_id]
    
    # Размер пропорционален ERS
    size = 100 + node["ers"] * 2
    
    # Цвет по секции
    color = section_colors.get(node["section"], "#FFFFFF")
    
    # Граница по блокеру
    edge_color = blocker_colors.get(node["blocker_type"], "#000000")
    
    # На критическом пути?
    if node_id in critical_path:
        edge_color = '#F44336'
        linewidth = 3
    else:
        linewidth = 1
    
    ax3.scatter(x, y, s=size, c=color, edgecolors=edge_color, linewidths=linewidth, zorder=5)
    
    # Подпись только для важных узлов
    if node["ers"] > 100 or node_id in critical_path:
        ax3.annotate(node_id.replace("_", "\n"), (x, y), fontsize=6, ha='center', va='center')

ax3.set_xlim(-0.5, max_depth + 0.5)
ax3.set_xlabel('Depth (Topological Level)', fontsize=12)
ax3.set_title('Dependency Graph with Critical Path\n(Red = Critical Path to RH)', fontsize=14, fontweight='bold')

# Легенда
legend_elements = [
    mpatches.Patch(facecolor=section_colors["5"], edgecolor='black', label='§5: Normalization'),
    mpatches.Patch(facecolor=section_colors["6"], edgecolor='black', label='§6: Density (A1\')'),
    mpatches.Patch(facecolor=section_colors["7"], edgecolor='black', label='§7: Continuity (A2)'),
    mpatches.Patch(facecolor=section_colors["8"], edgecolor='black', label='§8: Toeplitz (A3)'),
    mpatches.Patch(facecolor=section_colors["9"], edgecolor='black', label='§9: RKHS'),
    mpatches.Patch(facecolor=section_colors["10"], edgecolor='black', label='§10: D3'),
    mpatches.Patch(facecolor=section_colors["11"], edgecolor='black', label='§11: Main'),
    plt.Line2D([0], [0], color='#F44336', linewidth=2, label='Critical Path'),
]
ax3.legend(handles=legend_elements, loc='upper left', fontsize=8)

ax3.set_yticks([])
plt.tight_layout()
plt.savefig('/home/ubuntu/aristotle_research_package/rh_q3_analysis/dependency_graph.png', dpi=150, bbox_inches='tight')
print("Saved: dependency_graph.png")

# ============================================================================
# СОЗДАНИЕ ТАБЛИЦЫ ПЛАНА ФОРМАЛИЗАЦИИ
# ============================================================================

# Markdown таблица
markdown_output = """# План формализации RH_Q3.pdf в Lean

## Критический путь

```
thm_11_2 (RH) ← thm_11_4 (Main positivity) ← thm_8_35 (A3 bridge) 
    ← lemma_8_19 (Archimedean floor) ← lemma_8_14 (Archimedean floor)
    ← lemma_8_12 (Core contribution)
```

## Фазы формализации

"""

# Группируем по фазам (depth)
phases = defaultdict(list)
for n in data["nodes"]:
    phases[n["depth"]].append(n)

for phase in sorted(phases.keys()):
    nodes_in_phase = sorted(phases[phase], key=lambda x: x["ers"], reverse=True)
    markdown_output += f"### Фаза {phase + 1} ({len(nodes_in_phase)} узлов)\n\n"
    markdown_output += "| ID | Name | ERS | Type | Blocker |\n"
    markdown_output += "|---|---|---|---|---|\n"
    
    for n in nodes_in_phase:
        name_short = n["name"][:50] + "..." if len(n["name"]) > 50 else n["name"]
        markdown_output += f"| {n['id']} | {name_short} | {n['ers']:.1f} | {n['type']} | {n['blocker_type']} |\n"
    
    markdown_output += "\n"

# Статистика
markdown_output += """## Статистика

| Метрика | Значение |
|---|---|
"""
markdown_output += f"| Всего узлов | {len(data['nodes'])} |\n"
markdown_output += f"| Всего рёбер | {len(data['edges'])} |\n"
markdown_output += f"| Фаз формализации | {len(phases)} |\n"
markdown_output += f"| Суммарный ERS | {sum(n['ers'] for n in data['nodes']):.1f} |\n"
markdown_output += f"| Средний ERS | {sum(n['ers'] for n in data['nodes'])/len(data['nodes']):.1f} |\n"
markdown_output += f"| Максимальный ERS | {max(n['ers'] for n in data['nodes']):.1f} |\n"

# Hard blockers
hard_blockers = [n for n in data["nodes"] if n["blocker_type"] == "hard"]
markdown_output += f"| Hard blockers | {len(hard_blockers)} |\n"

with open("/home/ubuntu/aristotle_research_package/rh_q3_analysis/formalization_plan.md", "w") as f:
    f.write(markdown_output)

print("Saved: formalization_plan.md")
print("\nDone!")
