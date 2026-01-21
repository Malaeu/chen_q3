#!/usr/bin/env python3
"""
ЧИСЛЕННАЯ ПРОВЕРКА: Оператор B положительно определён?

B = i[F,U₂]χ₄ + (i[F,U₂]χ₄)†

Если B ≥ c·I с c > 0, то у нас есть forcing для TPC!
"""

import numpy as np
from scipy import linalg

def chi4(n):
    """Dirichlet character mod 4"""
    if n % 2 == 0:
        return 0
    elif n % 4 == 1:
        return 1
    else:
        return -1

def e(x):
    """e(x) = exp(2πix)"""
    return np.exp(2j * np.pi * x)

def build_F(X):
    """Phase operator F: F|n⟩ = e(n/4)|n⟩"""
    return np.diag([e(n/4) for n in range(X)])

def build_U2(X):
    """Shift operator U₂: U₂|n⟩ = |n+2⟩"""
    U = np.zeros((X, X), dtype=complex)
    for n in range(X - 2):
        U[n + 2, n] = 1.0
    return U

def build_chi4_diag(X):
    """χ₄ diagonal operator"""
    return np.diag([chi4(n) for n in range(X)])

def build_B(X):
    """
    B = i[F,U₂]χ₄ + (i[F,U₂]χ₄)†
    """
    F = build_F(X)
    U2 = build_U2(X)
    chi4_mat = build_chi4_diag(X)
    
    # Commutator [F, U₂]
    comm = F @ U2 - U2 @ F
    
    # A = [F,U₂]χ₄
    A = comm @ chi4_mat
    
    # B = i·A + (i·A)†
    iA = 1j * A
    B = iA + iA.conj().T
    
    return B

def von_mangoldt(n):
    """von Mangoldt function Λ(n)"""
    if n < 2:
        return 0.0
    # Check if n is prime power
    for p in range(2, int(np.sqrt(n)) + 1):
        if n % p == 0:
            # n is divisible by p, check if n = p^k
            k = 0
            m = n
            while m % p == 0:
                m //= p
                k += 1
            if m == 1:
                return np.log(p)
            else:
                return 0.0
    # n is prime
    return np.log(n)

def build_g(X):
    """Prime vector g_X = Σ_n Λ(n)|n⟩"""
    return np.array([von_mangoldt(n) for n in range(X)])

def S2(X):
    """Twin prime sum S₂(X) = Σ Λ(n)Λ(n+2)"""
    return sum(von_mangoldt(n) * von_mangoldt(n + 2) for n in range(X))

print("="*70)
print("ПРОВЕРКА ПОЗИТИВНОСТИ ОПЕРАТОРА B")
print("="*70)
print()

print("B = i[F,U₂]χ₄ + (i[F,U₂]χ₄)†")
print()

for X in [50, 100, 200, 500]:
    B = build_B(X)
    
    # Check Hermitian
    is_hermitian = np.allclose(B, B.conj().T)
    
    # Eigenvalues
    eigenvalues = linalg.eigvalsh(B)  # Real eigenvalues for Hermitian
    
    lambda_min = np.min(eigenvalues)
    lambda_max = np.max(eigenvalues)
    
    # Count positive, negative, zero eigenvalues
    n_pos = np.sum(eigenvalues > 1e-10)
    n_neg = np.sum(eigenvalues < -1e-10)
    n_zero = np.sum(np.abs(eigenvalues) <= 1e-10)
    
    # Check expectation value
    g = build_g(X)
    g_normalized = g / (np.linalg.norm(g) + 1e-10)
    expectation = np.real(g_normalized.conj() @ B @ g_normalized)
    
    s2 = S2(X)
    
    print(f"X = {X}:")
    print(f"  Hermitian: {is_hermitian}")
    print(f"  λ_min = {lambda_min:.6f}")
    print(f"  λ_max = {lambda_max:.6f}")
    print(f"  # positive: {n_pos}, # negative: {n_neg}, # zero: {n_zero}")
    print(f"  ⟨g_norm, B g_norm⟩ = {expectation:.6f}")
    print(f"  S₂(X) = {s2:.2f}")
    print()

print("="*70)
print("ВЫВОД")
print("="*70)
print()

# Larger test
X = 300
B = build_B(X)
eigenvalues = linalg.eigvalsh(B)
lambda_min = np.min(eigenvalues)
n_neg = np.sum(eigenvalues < -1e-10)

if n_neg > 0:
    print(f"""
❌ B НЕ ПОЛОЖИТЕЛЬНО ОПРЕДЕЛЁН!

При X = {X}:
  λ_min = {lambda_min:.6f} < 0
  Количество отрицательных собственных значений: {n_neg}

Это означает: ⟨v, Bv⟩ может быть < 0 для некоторых v.

Но! Проверим на prime subspace:
""")
    
    # Build projector onto primes
    primes = [n for n in range(2, X) if all(n % p != 0 for p in range(2, int(np.sqrt(n)) + 1))]
    P = np.zeros((X, X))
    for p in primes:
        if p < X:
            P[p, p] = 1
    
    # B restricted to primes
    B_primes = P @ B @ P
    B_primes_reduced = B_primes[primes][:, primes] if len(primes) > 0 else np.array([[0]])
    
    if B_primes_reduced.size > 1:
        eig_primes = linalg.eigvalsh(B_primes_reduced)
        lambda_min_primes = np.min(eig_primes)
        n_neg_primes = np.sum(eig_primes < -1e-10)
        
        print(f"На prime subspace (размерность {len(primes)}):")
        print(f"  λ_min = {lambda_min_primes:.6f}")
        print(f"  # negative: {n_neg_primes}")
        
        if n_neg_primes == 0:
            print("\n✅ B ≥ 0 на prime subspace!")
            print("Это может быть достаточно для forcing!")
        else:
            print("\n❌ B также не положительно определён на prime subspace.")

else:
    print(f"""
✅ B ПОЛОЖИТЕЛЬНО ПОЛУОПРЕДЕЛЁН!

При X = {X}:
  λ_min = {lambda_min:.6f} ≥ 0
  
Это даёт forcing: ⟨g, Bg⟩ ≥ 0 для всех g.
Но нужен СТРОГИЙ gap: λ_min > c > 0.
""")

print()
print("="*70)
print("АЛЬТЕРНАТИВА: B² ВСЕГДА ≥ 0")
print("="*70)
print()

X = 200
B = build_B(X)
B2 = B @ B

eigenvalues_B2 = linalg.eigvalsh(B2)
lambda_min_B2 = np.min(eigenvalues_B2)

g = build_g(X)
expectation_B2 = np.real(g.conj() @ B2 @ g)

print(f"B² при X = {X}:")
print(f"  λ_min(B²) = {lambda_min_B2:.6f} (должно быть ≥ 0)")
print(f"  ⟨g, B²g⟩ = {expectation_B2:.2f}")
print()
print("⟨g, B²g⟩ ≥ 0 автоматически, но это не даёт forcing на S₂.")
print("Нужна связь ⟨g, B²g⟩ = f(S₂) с f возрастающей.")
