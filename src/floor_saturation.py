import numpy as np
import matplotlib.pyplot as plt

def verify_floor_saturation():
    """
    Проверяет поведение НИЖНЕЙ ГРАНИЦЫ (Floor) символа P_A
    при расширении полосы пропускания B (что эквивалентно росту K).
    
    Цель: Опровергнуть гипотезу о том, что c_arch(K) -> 0.
    Ожидание: c_arch(K) монотонно растет и стремится к 1.
    """
    
    # Grid for theta [-pi, pi]
    theta = np.linspace(-np.pi, np.pi, 2000)
    
    B_values = [0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 50.0]
    
    results_B = []
    results_Floor = []
    results_Ceiling = []
    
    print(f"{'B':<10} | {'Floor (Min)':<15} | {'Ceiling (Max)':<15} | {'Gap Ratio':<15}")
    print("-" * 65)
    
    for B in B_values:
        P_A_vals = np.zeros_like(theta)
        N_tails = 500
        
        for n in range(-N_tails, N_tails + 1):
            xi = theta + 2 * np.pi * n
            
            # Base function: Lorentzian 1/(1+xi^2)
            a_base = 1.0 / (1.0 + xi**2)
            
            # Window function
            if B > 0:
                w_val = np.maximum(0.0, 1.0 - np.abs(xi)/B)
            else:
                w_val = 0.0
                
            term = a_base * w_val
            P_A_vals += term
            
        floor_val = np.min(P_A_vals)
        ceiling_val = np.max(P_A_vals)
        
        results_B.append(B)
        results_Floor.append(floor_val)
        results_Ceiling.append(ceiling_val)
        
        gap = floor_val / ceiling_val if ceiling_val > 0 else 0
        
        print(f"{B:<10.1f} | {floor_val:<15.4f} | {ceiling_val:<15.4f} | {gap:<15.4f}")

    return results_B, results_Floor, results_Ceiling

# --- EXECUTION ---
B_vals, floors, ceilings = verify_floor_saturation()

# --- VISUALIZATION ---
plt.figure(figsize=(10, 6))
plt.style.use('dark_background')

plt.plot(B_vals, floors, 'o-', color='lime', linewidth=2, label=r'Spectral Floor $c_{arch}(K)$ (Min)')
plt.plot(B_vals, ceilings, 'o-', color='cyan', linewidth=2, label=r'Spectral Ceiling $\|P_A\|_\infty$ (Max)')

# Asymptotic lines
plt.axhline(y=floors[-1], color='lime', linestyle='--', alpha=0.3)
plt.axhline(y=ceilings[-1], color='cyan', linestyle='--', alpha=0.3)

plt.title(r'Saturation of Spectral Floor $c_{arch}(K)$ as $K \to \infty$', fontsize=14)
plt.xlabel('Bandwidth Parameter B (proportional to K)')
plt.ylabel('Magnitude')
plt.legend()
plt.grid(True, alpha=0.2)
plt.tight_layout()
plt.savefig('floor_saturation.png', dpi=150)
print("\n✅ Saved: floor_saturation.png")
