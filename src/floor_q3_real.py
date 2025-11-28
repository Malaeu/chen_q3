import numpy as np
import matplotlib.pyplot as plt
import mpmath

"""
ИСПРАВЛЕННЫЙ ТЕСТ: Реальная функция из Q3

g(xi) = a(xi) * W(xi)
где:
  a(xi) = log(pi) - Re(psi(1/4 + i*pi*xi))
  W(xi) = (1 - |xi|/B) * exp(-4*pi^2*t*xi^2)

Проверяем: растёт ли Floor периодизации P_A(theta) с ростом B?
"""

pi = np.pi
t_sym = 0.7  # Параметр из Q3

def a_q3(xi):
    """Реальная функция a(xi) из Q3 через дигамму"""
    z = 0.25 + 1j * pi * xi
    return np.log(pi) - float(mpmath.re(mpmath.psi(0, z)))

def window_q3(xi, B):
    """Окно W(xi) = (1 - |xi|/B) * exp(-C*xi^2)"""
    C_gauss = 4 * (pi**2) * t_sym  # ~27.6
    
    # Triangular window (обнуляется при |xi| >= B)
    tri = max(0.0, 1.0 - abs(xi)/B)
    
    # Gaussian damping
    gauss = np.exp(-C_gauss * xi**2)
    
    return tri * gauss

def g_q3(xi, B):
    """Полная функция g(xi) = a(xi) * W(xi)"""
    return a_q3(xi) * window_q3(xi, B)

def compute_periodization(theta_val, B, N_tails=100):
    """
    P_A(theta) = sum_n g(theta + 2*pi*n)
    """
    total = 0.0
    for n in range(-N_tails, N_tails + 1):
        xi = theta_val + 2 * pi * n
        total += g_q3(xi, B)
    return total

# Test B values
B_values = [1.0, 2.0, 5.0, 10.0, 20.0, 50.0, 100.0]

# Grid for theta
theta_grid = np.linspace(-pi, pi, 200)

print(f"{'B':<10} | {'Floor (Min)':<15} | {'Ceiling (Max)':<15} | {'Ratio':<15}")
print("-" * 60)

results_B = []
results_Floor = []
results_Ceiling = []

for B in B_values:
    P_vals = []
    for th in theta_grid:
        P_vals.append(compute_periodization(th, B))
    
    P_vals = np.array(P_vals)
    floor_val = np.min(P_vals)
    ceiling_val = np.max(P_vals)
    ratio = floor_val / ceiling_val if ceiling_val != 0 else 0
    
    results_B.append(B)
    results_Floor.append(floor_val)
    results_Ceiling.append(ceiling_val)
    
    print(f"{B:<10.1f} | {floor_val:<15.6f} | {ceiling_val:<15.6f} | {ratio:<15.6f}")

# Visualization
plt.figure(figsize=(10, 6))
plt.style.use('dark_background')

plt.plot(results_B, results_Floor, 'o-', color='lime', linewidth=2, markersize=8, 
         label=r'Floor $\min_\theta P_A(\theta)$')
plt.plot(results_B, results_Ceiling, 'o-', color='cyan', linewidth=2, markersize=8,
         label=r'Ceiling $\max_\theta P_A(\theta)$')

plt.axhline(y=0, color='red', linestyle='--', alpha=0.5, label='Zero line')

plt.title(r'Q3 REAL: Floor Saturation with Digamma + Gaussian Window', fontsize=14)
plt.xlabel('Bandwidth B')
plt.ylabel('Periodization Value')
plt.legend()
plt.grid(True, alpha=0.2)
plt.tight_layout()
plt.savefig('floor_q3_real.png', dpi=150)
print("\n✅ Saved: floor_q3_real.png")
