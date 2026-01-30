#!/usr/bin/env python3.11
"""
Построение графа зависимостей для RH_Q3.pdf
и расчёт Effective Risk Score (ERS) для каждого узла.
"""

import json
from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, Optional
from collections import defaultdict
import math

@dataclass
class LemmaNode:
    """Узел в графе зависимостей"""
    id: str
    name: str
    section: str
    statement_type: str  # theorem, lemma, corollary, proposition, definition
    complexity: int  # 1-10
    uncertainty: int  # 1-10
    blocker_type: str  # none, soft, hard
    dependencies: List[str] = field(default_factory=list)
    used_by: List[str] = field(default_factory=list)
    constants: List[str] = field(default_factory=list)
    
    # Computed fields
    raw_risk: float = 0.0
    inherited_risk: float = 0.0
    critical_path_bonus: float = 0.0
    ers: float = 0.0
    depth: int = 0
    centrality: float = 0.0

# ============================================================================
# ОПРЕДЕЛЕНИЕ ВСЕХ УЗЛОВ
# ============================================================================

nodes: Dict[str, LemmaNode] = {}

# --- Секция 5: Normalization (T0) ---
nodes["prop_5_1"] = LemmaNode(
    id="prop_5_1",
    name="Proposition 5.1 (T0' — Guinand-Weil matching)",
    section="5",
    statement_type="proposition",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=[],
    constants=[]
)

nodes["lemma_5_2"] = LemmaNode(
    id="lemma_5_2",
    name="Lemma 5.2 (T0: Q normalization crosswalk)",
    section="5",
    statement_type="lemma",
    complexity=4,
    uncertainty=2,
    blocker_type="none",
    dependencies=["prop_5_1"],
    constants=[]
)

nodes["lemma_5_3"] = LemmaNode(
    id="lemma_5_3",
    name="Lemma 5.3 (Invariance under normalisation conventions)",
    section="5",
    statement_type="lemma",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=["lemma_5_2"],
    constants=[]
)

# --- Секция 6: Local Density (A1') ---
nodes["lemma_6_2"] = LemmaNode(
    id="lemma_6_2",
    name="Lemma 6.2 (Compact support convolution reduction)",
    section="6",
    statement_type="lemma",
    complexity=2,
    uncertainty=1,
    blocker_type="none",
    dependencies=[],
    constants=[]
)

nodes["thm_6_3"] = LemmaNode(
    id="thm_6_3",
    name="Theorem 6.3 (A1' — density)",
    section="6",
    statement_type="theorem",
    complexity=5,
    uncertainty=3,
    blocker_type="soft",
    dependencies=["lemma_6_2"],
    constants=["B", "t", "tau"]
)

# --- Секция 7: Continuity of Q (A2) ---
nodes["lemma_7_1"] = LemmaNode(
    id="lemma_7_1",
    name="Lemma 7.1 (Local finiteness of the prime sampler)",
    section="7",
    statement_type="lemma",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=[],
    constants=["K"]
)

nodes["cor_7_2"] = LemmaNode(
    id="cor_7_2",
    name="Corollary 7.2 (Lipschitz continuity on a compact window)",
    section="7",
    statement_type="corollary",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=["lemma_7_1"],
    constants=["K"]
)

nodes["lemma_7_3"] = LemmaNode(
    id="lemma_7_3",
    name="Lemma 7.3 (A2 — Lipschitz on C^+_even(K))",
    section="7",
    statement_type="lemma",
    complexity=4,
    uncertainty=2,
    blocker_type="none",
    dependencies=["lemma_7_1"],
    constants=["L_Q(K)"]
)

nodes["cor_7_4"] = LemmaNode(
    id="cor_7_4",
    name="Corollary 7.4 (Explicit Lipschitz modulus for Q)",
    section="7",
    statement_type="corollary",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=["cor_7_2", "lemma_7_3"],
    constants=["L_Q(K)"]
)

# --- Секция 8: Toeplitz-Symbol Bridge (A3) ---
nodes["lemma_8_1"] = LemmaNode(
    id="lemma_8_1",
    name="Lemma 8.1 (Period-1 normalization audit)",
    section="8",
    statement_type="lemma",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=[],
    constants=[]
)

nodes["lemma_8_2"] = LemmaNode(
    id="lemma_8_2",
    name="Lemma 8.2 (Calibration of κ_{A3})",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=["lemma_8_1"],
    constants=["kappa_A3"]
)

nodes["lemma_8_3"] = LemmaNode(
    id="lemma_8_3",
    name="Lemma 8.3 (Rayleigh identification)",
    section="8",
    statement_type="lemma",
    complexity=5,
    uncertainty=3,
    blocker_type="soft",
    dependencies=["lemma_8_2"],
    constants=[]
)

nodes["lemma_8_5"] = LemmaNode(
    id="lemma_8_5",
    name="Lemma 8.5 (Lipschitz modulus for the periodized symbol)",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=[],
    constants=["L_A(B,t)"]
)

nodes["lemma_8_12"] = LemmaNode(
    id="lemma_8_12",
    name="Lemma 8.12 (Core contribution)",
    section="8",
    statement_type="lemma",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=[],
    constants=["m_r", "M_B"]
)

nodes["lemma_8_13"] = LemmaNode(
    id="lemma_8_13",
    name="Lemma 8.13 (Shift-robust core mass)",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=[],
    constants=[]
)

nodes["lemma_8_14"] = LemmaNode(
    id="lemma_8_14",
    name="Lemma 8.14 (Archimedean floor)",
    section="8",
    statement_type="lemma",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_8_12", "lemma_8_13"],
    constants=["L_A^up", "A_0"]
)

nodes["lemma_8_15"] = LemmaNode(
    id="lemma_8_15",
    name="Lemma 8.15 (Core slope bound)",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=[],
    constants=["L_a", "a(0)"]
)

nodes["lemma_8_16"] = LemmaNode(
    id="lemma_8_16",
    name="Lemma 8.16 (Digamma monotonicity)",
    section="8",
    statement_type="lemma",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=[],
    constants=[]
)

nodes["lemma_8_17"] = LemmaNode(
    id="lemma_8_17",
    name="Lemma 8.17 (Logarithmic growth bound)",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=["lemma_8_16"],
    constants=[]
)

nodes["lemma_8_18"] = LemmaNode(
    id="lemma_8_18",
    name="Lemma 8.18 (Sample-point bounds for a)",
    section="8",
    statement_type="lemma",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=[],
    constants=["a(1/2)", "a(3/2)", "a(5/2)"]
)

nodes["lemma_8_19"] = LemmaNode(
    id="lemma_8_19",
    name="Lemma 8.19 (Uniform Archimedean floor)",
    section="8",
    statement_type="lemma",
    complexity=6,
    uncertainty=5,
    blocker_type="hard",
    dependencies=["lemma_8_14", "lemma_8_15", "lemma_8_17", "lemma_8_18"],
    constants=["c_*", "t_sym", "B_min"]
)

nodes["def_8_20"] = LemmaNode(
    id="def_8_20",
    name="Definition 8.20 (Uniform Lipschitz constant)",
    section="8",
    statement_type="definition",
    complexity=2,
    uncertainty=1,
    blocker_type="none",
    dependencies=["lemma_8_5"],
    constants=["L_A", "L_*"]
)

nodes["cor_8_21"] = LemmaNode(
    id="cor_8_21",
    name="Corollary 8.21 (Uniform discretisation threshold)",
    section="8",
    statement_type="corollary",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_8_19", "lemma_8_30"],
    constants=["M_0^unif"]
)

nodes["cor_8_22"] = LemmaNode(
    id="cor_8_22",
    name="Corollary 8.22 (Uniform prime cap time)",
    section="8",
    statement_type="corollary",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_8_19", "lemma_9_24"],
    constants=["t^unif_*,rkhs"]
)

nodes["lemma_8_23"] = LemmaNode(
    id="lemma_8_23",
    name="Lemma 8.23 (Analytic mean bound)",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=["lemma_8_15"],
    constants=["A_*", "alpha"]
)

nodes["lemma_8_24"] = LemmaNode(
    id="lemma_8_24",
    name="Lemma 8.24 (Analytic Lipschitz bound)",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=["lemma_8_23", "def_8_20"],
    constants=["L_up"]
)

nodes["lemma_8_30"] = LemmaNode(
    id="lemma_8_30",
    name="Lemma 8.30 (Szegő-Böttcher discretisation)",
    section="8",
    statement_type="lemma",
    complexity=6,
    uncertainty=5,
    blocker_type="hard",
    dependencies=[],
    constants=["C_SB"]
)

nodes["prop_8_4"] = LemmaNode(
    id="prop_8_4",
    name="Proposition 8.4 (Bridge margin calibration)",
    section="8",
    statement_type="proposition",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_8_19", "thm_8_35", "cor_8_21", "cor_8_22"],
    constants=[]
)

nodes["thm_8_35"] = LemmaNode(
    id="thm_8_35",
    name="Theorem 8.35 (Uniform A3 bridge)",
    section="8",
    statement_type="theorem",
    complexity=8,
    uncertainty=6,
    blocker_type="hard",
    dependencies=["lemma_8_19", "cor_8_21", "cor_8_22", "lemma_8_5", "lemma_8_24", "prop_9_3", "thm_9_6"],
    constants=["c_*", "B_min", "M_0^unif"]
)

# --- Секция 9: RKHS Contraction ---
nodes["lemma_9_1"] = LemmaNode(
    id="lemma_9_1",
    name="Lemma 9.1 (Gershgorin floor)",
    section="9",
    statement_type="lemma",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=[],
    constants=[]
)

nodes["lemma_9_2"] = LemmaNode(
    id="lemma_9_2",
    name="Lemma 9.2 (Spectral floor for Gram matrices)",
    section="9",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=["lemma_9_1"],
    constants=[]
)

nodes["prop_9_3"] = LemmaNode(
    id="prop_9_3",
    name="Proposition 9.3 (Operator sandwich)",
    section="9",
    statement_type="proposition",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_9_2"],
    constants=[]
)

nodes["lemma_9_4"] = LemmaNode(
    id="lemma_9_4",
    name="Lemma 9.4 (Rayleigh sampling identification)",
    section="9",
    statement_type="lemma",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_8_3"],
    constants=[]
)

nodes["lemma_9_5"] = LemmaNode(
    id="lemma_9_5",
    name="Lemma 9.5 (Geometric tail bound for S_K(t))",
    section="9",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=[],
    constants=["delta_K"]
)

nodes["thm_9_6"] = LemmaNode(
    id="thm_9_6",
    name="Theorem 9.6 (Strict contraction)",
    section="9",
    statement_type="theorem",
    complexity=6,
    uncertainty=5,
    blocker_type="hard",
    dependencies=["lemma_9_5"],
    constants=["rho_K"]
)

nodes["prop_9_7"] = LemmaNode(
    id="prop_9_7",
    name="Proposition 9.7 (Dataset-free RKHS schedule)",
    section="9",
    statement_type="proposition",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_9_5"],
    constants=["t_min(K)", "eta_K"]
)

nodes["lemma_9_8"] = LemmaNode(
    id="lemma_9_8",
    name="Lemma 9.8 (Effective weight cap)",
    section="9",
    statement_type="lemma",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=[],
    constants=["w_max"]
)

nodes["lemma_9_10"] = LemmaNode(
    id="lemma_9_10",
    name="Lemma 9.10 (Node gap on compacts)",
    section="9",
    statement_type="lemma",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=[],
    constants=["delta_K"]
)

nodes["cor_9_11"] = LemmaNode(
    id="cor_9_11",
    name="Corollary 9.11 (Two-scale decoupling)",
    section="9",
    statement_type="corollary",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_9_8", "cor_8_22"],
    constants=[]
)

nodes["thm_9_12"] = LemmaNode(
    id="thm_9_12",
    name="Theorem 9.12 (One-prime induction)",
    section="9",
    statement_type="theorem",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_9_8"],
    constants=[]
)

nodes["lemma_9_13"] = LemmaNode(
    id="lemma_9_13",
    name="Lemma 9.13 (Node separation)",
    section="9",
    statement_type="lemma",
    complexity=3,
    uncertainty=2,
    blocker_type="none",
    dependencies=[],
    constants=["delta_K"]
)

nodes["lemma_9_24"] = LemmaNode(
    id="lemma_9_24",
    name="Lemma 9.24 (Gaussian norm cap)",
    section="9",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=[],
    constants=["rho(t)"]
)

# --- Секция 10: Prime Cancellation (D3) ---
nodes["lemma_10_1"] = LemmaNode(
    id="lemma_10_1",
    name="Lemma 10.1 (Dispersion via A2/A3 data)",
    section="10",
    statement_type="lemma",
    complexity=6,
    uncertainty=5,
    blocker_type="hard",
    dependencies=["lemma_8_11", "lemma_8_33", "cor_8_22", "lemma_8_32"],
    constants=["delta_A"]
)

nodes["lemma_8_11"] = LemmaNode(
    id="lemma_8_11",
    name="Lemma 8.11 (Lipschitz symbol P_A)",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=["lemma_8_5"],
    constants=[]
)

nodes["lemma_8_32"] = LemmaNode(
    id="lemma_8_32",
    name="Lemma 8.32 (Two-scale separation)",
    section="8",
    statement_type="lemma",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=[],
    constants=[]
)

nodes["lemma_8_33"] = LemmaNode(
    id="lemma_8_33",
    name="Lemma 8.33 (min P_A bound)",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=["lemma_8_19"],
    constants=[]
)

nodes["lemma_8_34"] = LemmaNode(
    id="lemma_8_34",
    name="Lemma 8.34 (Modulus control)",
    section="8",
    statement_type="lemma",
    complexity=4,
    uncertainty=3,
    blocker_type="none",
    dependencies=["lemma_8_24"],
    constants=[]
)

nodes["thm_10_2"] = LemmaNode(
    id="thm_10_2",
    name="Theorem 10.2 (D3: Structural contraction)",
    section="10",
    statement_type="theorem",
    complexity=7,
    uncertainty=5,
    blocker_type="hard",
    dependencies=["lemma_10_1"],
    constants=["delta_0", "C_D3"]
)

nodes["cor_10_3"] = LemmaNode(
    id="cor_10_3",
    name="Corollary 10.3 (Amplitude closure)",
    section="10",
    statement_type="corollary",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["thm_10_2"],
    constants=["Gamma(K)"]
)

nodes["thm_10_6"] = LemmaNode(
    id="thm_10_6",
    name="Theorem 10.6 (Structural prime cancellation)",
    section="10",
    statement_type="theorem",
    complexity=7,
    uncertainty=5,
    blocker_type="hard",
    dependencies=["lemma_8_11", "lemma_8_33", "lemma_8_34", "lemma_8_32", "cor_8_22", "lemma_10_1"],
    constants=[]
)

nodes["prop_10_8"] = LemmaNode(
    id="prop_10_8",
    name="Proposition 10.8 (AB(K) supplied by A3)",
    section="10",
    statement_type="proposition",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["lemma_8_19", "lemma_8_11", "lemma_8_34", "lemma_8_32"],
    constants=[]
)

nodes["thm_10_9"] = LemmaNode(
    id="thm_10_9",
    name="Theorem 10.9 (Amplitude gate without D3)",
    section="10",
    statement_type="theorem",
    complexity=6,
    uncertainty=5,
    blocker_type="hard",
    dependencies=["prop_10_8", "cor_8_31"],
    constants=[]
)

nodes["cor_8_31"] = LemmaNode(
    id="cor_8_31",
    name="Corollary 8.31 (Mixed lower bound)",
    section="8",
    statement_type="corollary",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["cor_8_21"],
    constants=[]
)

# --- Секция 11: Main Theorem ---
nodes["thm_11_1"] = LemmaNode(
    id="thm_11_1",
    name="Theorem 11.1 (Weil's positivity criterion)",
    section="11",
    statement_type="theorem",
    complexity=3,
    uncertainty=1,
    blocker_type="none",
    dependencies=[],  # Классический результат
    constants=[]
)

nodes["thm_11_2"] = LemmaNode(
    id="thm_11_2",
    name="Theorem 11.2 (Riemann Hypothesis)",
    section="11",
    statement_type="theorem",
    complexity=2,
    uncertainty=1,
    blocker_type="none",
    dependencies=["thm_11_4", "thm_11_1"],
    constants=[]
)

nodes["thm_11_3"] = LemmaNode(
    id="thm_11_3",
    name="Theorem 11.3 (Weil sufficiency pack)",
    section="11",
    statement_type="theorem",
    complexity=6,
    uncertainty=4,
    blocker_type="soft",
    dependencies=["thm_11_4", "thm_6_3", "lemma_7_3", "thm_8_35", "cor_8_22", "lemma_9_23", "lemma_9_4"],
    constants=[]
)

nodes["lemma_9_23"] = LemmaNode(
    id="lemma_9_23",
    name="Lemma 9.23 (RKHS-Weil isometry)",
    section="9",
    statement_type="lemma",
    complexity=5,
    uncertainty=4,
    blocker_type="soft",
    dependencies=[],
    constants=[]
)

nodes["thm_11_4"] = LemmaNode(
    id="thm_11_4",
    name="Theorem 11.4 (Main positivity on W)",
    section="11",
    statement_type="theorem",
    complexity=7,
    uncertainty=5,
    blocker_type="hard",
    dependencies=["thm_8_35", "thm_6_3", "lemma_7_3", "prop_5_1", "cor_8_22"],
    constants=[]
)

# ============================================================================
# ПОСТРОЕНИЕ ОБРАТНЫХ СВЯЗЕЙ (used_by)
# ============================================================================

def build_reverse_edges():
    """Построить обратные рёбра (used_by) из зависимостей"""
    for node_id, node in nodes.items():
        for dep_id in node.dependencies:
            if dep_id in nodes:
                nodes[dep_id].used_by.append(node_id)

build_reverse_edges()

# ============================================================================
# РАСЧЁТ ГЛУБИНЫ (ТОПОЛОГИЧЕСКАЯ СОРТИРОВКА)
# ============================================================================

def calculate_depths():
    """Вычислить глубину каждого узла (максимальное расстояние от корней)"""
    # Находим корни (узлы без зависимостей)
    roots = [nid for nid, n in nodes.items() if len(n.dependencies) == 0]
    
    # BFS для вычисления глубины
    from collections import deque
    
    for nid in roots:
        nodes[nid].depth = 0
    
    # Многократный проход для учёта всех путей
    changed = True
    while changed:
        changed = False
        for nid, node in nodes.items():
            if node.dependencies:
                max_dep_depth = max(
                    nodes[dep].depth for dep in node.dependencies if dep in nodes
                )
                new_depth = max_dep_depth + 1
                if new_depth > node.depth:
                    node.depth = new_depth
                    changed = True

calculate_depths()

# ============================================================================
# РАСЧЁТ ЦЕНТРАЛЬНОСТИ
# ============================================================================

def calculate_centrality():
    """Вычислить центральность узла (сколько узлов от него зависят)"""
    def count_descendants(node_id: str, visited: Set[str]) -> int:
        if node_id in visited:
            return 0
        visited.add(node_id)
        count = 1
        for child_id in nodes[node_id].used_by:
            if child_id in nodes:
                count += count_descendants(child_id, visited)
        return count
    
    for nid, node in nodes.items():
        visited = set()
        node.centrality = count_descendants(nid, visited) - 1  # Не считаем сам узел

calculate_centrality()

# ============================================================================
# РАСЧЁТ RAW RISK SCORE
# ============================================================================

def calculate_raw_risk():
    """Вычислить Raw Risk Score для каждого узла"""
    blocker_weights = {"none": 1.0, "soft": 1.5, "hard": 2.0}
    
    for nid, node in nodes.items():
        # Raw Risk = complexity * uncertainty * blocker_weight * (1 + centrality/10)
        blocker_w = blocker_weights.get(node.blocker_type, 1.0)
        centrality_factor = 1 + node.centrality / 10
        node.raw_risk = node.complexity * node.uncertainty * blocker_w * centrality_factor

calculate_raw_risk()

# ============================================================================
# РАСЧЁТ INHERITED RISK
# ============================================================================

def calculate_inherited_risk():
    """Вычислить унаследованный риск от зависимостей"""
    # Топологическая сортировка
    from collections import deque
    
    in_degree = {nid: len(n.dependencies) for nid, n in nodes.items()}
    queue = deque([nid for nid, deg in in_degree.items() if deg == 0])
    
    while queue:
        nid = queue.popleft()
        node = nodes[nid]
        
        # Унаследованный риск = сумма (raw_risk + inherited_risk) зависимостей * 0.3
        if node.dependencies:
            inherited = sum(
                (nodes[dep].raw_risk + nodes[dep].inherited_risk) * 0.3
                for dep in node.dependencies if dep in nodes
            )
            node.inherited_risk = inherited
        
        # Уменьшаем in_degree для детей
        for child_id in node.used_by:
            if child_id in nodes:
                in_degree[child_id] -= 1
                if in_degree[child_id] == 0:
                    queue.append(child_id)

calculate_inherited_risk()

# ============================================================================
# РАСЧЁТ CRITICAL PATH BONUS
# ============================================================================

def calculate_critical_path():
    """Найти критический путь и добавить бонус"""
    # Критический путь = путь с максимальной суммой (raw_risk + inherited_risk)
    
    # Находим конечные узлы (без used_by)
    terminals = [nid for nid, n in nodes.items() if len(n.used_by) == 0]
    
    # Для каждого узла вычисляем максимальный путь до терминала
    max_path_to_terminal = {}
    
    def get_max_path(nid: str) -> float:
        if nid in max_path_to_terminal:
            return max_path_to_terminal[nid]
        
        node = nodes[nid]
        if not node.used_by:
            max_path_to_terminal[nid] = node.raw_risk
            return node.raw_risk
        
        max_child_path = max(get_max_path(child) for child in node.used_by if child in nodes)
        max_path_to_terminal[nid] = node.raw_risk + max_child_path
        return max_path_to_terminal[nid]
    
    # Вычисляем для всех узлов
    for nid in nodes:
        get_max_path(nid)
    
    # Находим глобальный максимум
    max_total = max(max_path_to_terminal.values()) if max_path_to_terminal else 1
    
    # Бонус = 20% от raw_risk для узлов на критическом пути (top 20% по max_path)
    threshold = max_total * 0.8
    for nid, path_value in max_path_to_terminal.items():
        if path_value >= threshold:
            nodes[nid].critical_path_bonus = nodes[nid].raw_risk * 0.2

calculate_critical_path()

# ============================================================================
# РАСЧЁТ ERS
# ============================================================================

def calculate_ers():
    """Вычислить Effective Risk Score"""
    for nid, node in nodes.items():
        node.ers = node.raw_risk + node.inherited_risk + node.critical_path_bonus

calculate_ers()

# ============================================================================
# ВЫВОД РЕЗУЛЬТАТОВ
# ============================================================================

def print_results():
    """Вывести результаты анализа"""
    print("=" * 80)
    print("ГРАФ ЗАВИСИМОСТЕЙ RH_Q3.pdf — АНАЛИЗ ERS")
    print("=" * 80)
    print()
    
    # Сортируем по ERS (убывание)
    sorted_nodes = sorted(nodes.values(), key=lambda n: n.ers, reverse=True)
    
    print("TOP-20 УЗЛОВ ПО ERS (приоритет формализации):")
    print("-" * 80)
    print(f"{'#':<3} {'ID':<15} {'ERS':<8} {'Raw':<8} {'Inh':<8} {'CPB':<6} {'Depth':<6} {'Type':<12}")
    print("-" * 80)
    
    for i, node in enumerate(sorted_nodes[:20], 1):
        print(f"{i:<3} {node.id:<15} {node.ers:<8.1f} {node.raw_risk:<8.1f} "
              f"{node.inherited_risk:<8.1f} {node.critical_path_bonus:<6.1f} "
              f"{node.depth:<6} {node.statement_type:<12}")
    
    print()
    print("=" * 80)
    print("КРИТИЧЕСКИЙ ПУТЬ (от корней до главной теоремы):")
    print("=" * 80)
    
    # Восстанавливаем критический путь
    def find_critical_path(target: str) -> List[str]:
        path = [target]
        current = target
        while nodes[current].dependencies:
            # Выбираем зависимость с максимальным ERS
            deps = [d for d in nodes[current].dependencies if d in nodes]
            if not deps:
                break
            next_node = max(deps, key=lambda d: nodes[d].ers)
            path.append(next_node)
            current = next_node
        return list(reversed(path))
    
    critical_path = find_critical_path("thm_11_2")
    print(" → ".join(critical_path))
    print()
    
    total_ers = sum(nodes[nid].ers for nid in critical_path)
    print(f"Суммарный ERS критического пути: {total_ers:.1f}")
    print()
    
    # Статистика по секциям
    print("=" * 80)
    print("СТАТИСТИКА ПО СЕКЦИЯМ:")
    print("=" * 80)
    
    section_stats = defaultdict(lambda: {"count": 0, "total_ers": 0, "max_ers": 0})
    for node in nodes.values():
        section_stats[node.section]["count"] += 1
        section_stats[node.section]["total_ers"] += node.ers
        section_stats[node.section]["max_ers"] = max(section_stats[node.section]["max_ers"], node.ers)
    
    print(f"{'Section':<10} {'Count':<8} {'Total ERS':<12} {'Max ERS':<10} {'Avg ERS':<10}")
    print("-" * 50)
    for section in sorted(section_stats.keys()):
        stats = section_stats[section]
        avg = stats["total_ers"] / stats["count"] if stats["count"] > 0 else 0
        print(f"{section:<10} {stats['count']:<8} {stats['total_ers']:<12.1f} "
              f"{stats['max_ers']:<10.1f} {avg:<10.1f}")
    
    return sorted_nodes

sorted_nodes = print_results()

# ============================================================================
# ЭКСПОРТ В JSON
# ============================================================================

def export_to_json():
    """Экспортировать граф в JSON для визуализации"""
    export_data = {
        "nodes": [],
        "edges": []
    }
    
    for nid, node in nodes.items():
        export_data["nodes"].append({
            "id": node.id,
            "name": node.name,
            "section": node.section,
            "type": node.statement_type,
            "complexity": node.complexity,
            "uncertainty": node.uncertainty,
            "blocker_type": node.blocker_type,
            "raw_risk": round(node.raw_risk, 2),
            "inherited_risk": round(node.inherited_risk, 2),
            "critical_path_bonus": round(node.critical_path_bonus, 2),
            "ers": round(node.ers, 2),
            "depth": node.depth,
            "centrality": node.centrality
        })
        
        for dep in node.dependencies:
            if dep in nodes:
                export_data["edges"].append({
                    "source": dep,
                    "target": nid
                })
    
    with open("/home/ubuntu/aristotle_research_package/rh_q3_analysis/dependency_graph.json", "w") as f:
        json.dump(export_data, f, indent=2)
    
    print()
    print("Граф экспортирован в dependency_graph.json")

export_to_json()

# ============================================================================
# ГЕНЕРАЦИЯ ПЛАНА ФОРМАЛИЗАЦИИ
# ============================================================================

def generate_formalization_plan():
    """Генерировать план формализации в порядке топологической сортировки"""
    print()
    print("=" * 80)
    print("ПЛАН ФОРМАЛИЗАЦИИ В LEAN (топологический порядок)")
    print("=" * 80)
    print()
    
    # Топологическая сортировка с учётом ERS внутри уровня
    from collections import deque
    
    in_degree = {nid: len([d for d in n.dependencies if d in nodes]) for nid, n in nodes.items()}
    available = [nid for nid, deg in in_degree.items() if deg == 0]
    
    order = []
    phase = 1
    
    while available:
        # Сортируем доступные по ERS (убывание) — приоритет высокорисковым
        available.sort(key=lambda x: nodes[x].ers, reverse=True)
        
        print(f"ФАЗА {phase}: {len(available)} узлов")
        print("-" * 40)
        
        for nid in available:
            node = nodes[nid]
            print(f"  [{node.ers:.1f}] {node.id}: {node.name[:50]}...")
            order.append(nid)
        
        print()
        
        # Обновляем in_degree
        next_available = []
        for nid in available:
            for child in nodes[nid].used_by:
                if child in nodes:
                    in_degree[child] -= 1
                    if in_degree[child] == 0:
                        next_available.append(child)
        
        available = next_available
        phase += 1
    
    return order

formalization_order = generate_formalization_plan()

print()
print(f"Всего узлов для формализации: {len(formalization_order)}")
print(f"Всего фаз: {max(n.depth for n in nodes.values()) + 1}")
