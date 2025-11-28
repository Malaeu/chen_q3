import numpy as np
import matplotlib.pyplot as plt
import mpmath

# --- SETUP ---
t_sym = 0.7
pi = np.pi

# Список значений B для проверки (от Q3-минимума до "бесконечности")
B_values = [1.0/3.0, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0]

def get_derivatives_at_point(xi, B_curr):
    """
    Вычисляет значения g, g', g'' в точке xi для текущего B.
    """
    # 1. a(xi) parts
    z = 0.25 + 1j * pi * xi
    val_a = np.log(pi) - float(mpmath.re(mpmath.psi(0, z)))
    psi_1 = mpmath.psi(1, z)
    val_da = float(mpmath.im(psi_1)) * pi
    psi_2 = mpmath.psi(2, z)
    val_dda = float(mpmath.re(psi_2)) * (pi**2)
    
    # 2. Window parts W(xi) = (1 - xi/B) * E
    # E = exp(-C * xi^2)
    C_gauss = 4 * (pi**2) * t_sym
    E = np.exp(-C_gauss * (xi**2))
    
    # W derivatives
    # W = (1 - xi/B) * E
    L = (1 - xi/B_curr)
    dL = -1.0/B_curr
    ddL = 0
    
    # E derivatives
    # E' = -2*C*xi * E
    factor = -2 * C_gauss * xi
    dE = factor * E
    # E'' = (-2*C + factor^2) * E
    ddE = (-2 * C_gauss + factor**2) * E
    
    W = L * E
    dW = dL * E + L * dE
    ddW = ddL*E + 2*dL*dE + L*ddE
    
    # 3. Combine g = a*W
    g = val_a * W
    dg = val_da * W + val_a * dW
    ddg = val_dda * W + 2*val_da * dW + val_a * ddW
    
    return abs(g), abs(dg), abs(ddg)

results_B = []
results_Norm = []

print(f"{'B':<10} | {'A0 (Integral)':<15} | {'Tail Bound':<15} | {'TOTAL C0':<15}")
print("-" * 65)

for B in B_values:
    limit = min(B, 1.5) 
    N_points = 1000
    xi_vals = np.linspace(0, limit, N_points)
    
    g_vals = []
    ddg_vals = []
    
    # Boundary terms for Tail Formula
    _, dg_0, _ = get_derivatives_at_point(0, B)
    _, dg_B, _ = get_derivatives_at_point(B, B)
    
    # Scan integral
    for xi in xi_vals:
        g, dg, ddg = get_derivatives_at_point(xi, B)
        g_vals.append(g)
        ddg_vals.append(ddg)
        
    # 1. Calculate A0 via Integration
    integral_g = np.trapz(g_vals, xi_vals)
    A0_val = 2 * integral_g
    
    # 2. Calculate Tail Bound via Second Derivative Integral
    integral_ddg = np.trapz(ddg_vals, xi_vals)
    
    numerator = dg_0 + dg_B + integral_ddg
    tail_sum = 2 * numerator * (pi**2 / 6)
    
    # 3. Total
    total_C0 = A0_val + tail_sum
    
    results_B.append(B)
    results_Norm.append(total_C0)
    
    print(f"{B:<10.3f} | {A0_val:<15.4f} | {tail_sum:<15.4f} | {total_C0:<15.4f}")

# Plotting the Saturation
plt.figure(figsize=(10, 6))
plt.style.use('dark_background')
plt.plot(results_B, results_Norm, 'o-', color='cyan', linewidth=2, markersize=8)
plt.axhline(y=results_Norm[-1], color='magenta', linestyle='--', alpha=0.5, label='Asymptotic Ceiling')
plt.title(r'Saturation of Symbol Norm $C_0(B)$ as $B \to \infty$', fontsize=14)
plt.xlabel('Bandwidth Parameter B (proportional to K)')
plt.ylabel(r'Proven Upper Bound $C_0$')
plt.grid(True, alpha=0.2)
plt.legend()
plt.tight_layout()
plt.savefig('saturation_proof.png', dpi=150)
print("\n✅ Saved: saturation_proof.png")
