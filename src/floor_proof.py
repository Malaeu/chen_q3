import numpy as np
import matplotlib.pyplot as plt

def check_spectral_floor(B_values):
    """
    Проверяет поведение МИНИМУМА символа P_A (Archimedean Floor)
    при расширении полосы пропускания B.
    """
    
    results = {
        'B': [],
        'Floor_Min': [],
        'Ceiling_Max': [],
        'Gap_Ratio': []
    }
    
    # Grid on [-pi, pi]
    theta = np.linspace(-np.pi, np.pi, 5000)
    
    max_ref = None
    
    for B in B_values:
        P_A_vals = np.zeros_like(theta)
        
        N_tails = 1000
        for n in range(-N_tails, N_tails + 1):
            xi = theta + 2 * np.pi * n
            
            # Base function (Lorentzian - аналог дигаммы)
            a_base = 1.0 / (1.0 + xi**2) 
            
            # Window function (как в Q3)
            # W(xi) = (1 - |xi|/B) при |xi| < B, иначе 0
            w_val = np.maximum(0, 1.0 - np.abs(xi)/B)
            
            # Symbol term
            term = a_base * w_val
            P_A_vals += term
            
        # Нормируем на "идеальную сумму" (при B=inf)
        if max_ref is None:
             # Считаем референс один раз
             P_ref = np.zeros_like(theta)
             for n in range(-N_tails, N_tails + 1):
                 xi = theta + 2 * np.pi * n
                 P_ref += 1.0 / (1.0 + xi**2)
             max_ref = np.max(P_ref)
        
        # Нормировка
        P_A_vals /= max_ref
        
        floor = np.min(P_A_vals)
        ceiling = np.max(P_A_vals)
        
        results['B'].append(B)
        results['Floor_Min'].append(floor)
        results['Ceiling_Max'].append(ceiling)
        results['Gap_Ratio'].append(floor / ceiling)

    return results

# Запуск
B_list = [1.0, 2.0, 5.0, 10.0, 20.0, 50.0, 100.0]
data = check_spectral_floor(B_list)

# Print results
print(f"{'B':<10} | {'Floor':<12} | {'Ceiling':<12} | {'Ratio':<12}")
print("-" * 50)
for i in range(len(data['B'])):
    print(f"{data['B'][i]:<10.1f} | {data['Floor_Min'][i]:<12.6f} | {data['Ceiling_Max'][i]:<12.6f} | {data['Gap_Ratio'][i]:<12.6f}")

# Визуализация
plt.style.use('dark_background')
plt.figure(figsize=(10, 6))

plt.plot(data['B'], data['Floor_Min'], 'o-', color='lime', linewidth=2, label=r'Spectral Floor $c_{arch}(K)$')
plt.plot(data['B'], data['Ceiling_Max'], 'o-', color='cyan', linewidth=2, label=r'Spectral Ceiling $\|P_A\|_\infty$')
plt.axhline(y=1.0, color='white', linestyle=':', alpha=0.5)

plt.title(r'Монотонность Пола: $c_{arch}(K)$ растет с $K$', fontsize=14)
plt.xlabel('Bandwidth B (proportional to K)')
plt.ylabel('Normalized Magnitude')
plt.legend()
plt.grid(True, alpha=0.2)
plt.tight_layout()
plt.savefig('floor_proof.png', dpi=150)
print("\n✅ Saved: floor_proof.png")
