# Q3 Twins Mod 6 Structure Theorem

## Setup

Define:
- Twin primes: T = {p : ℕ | Prime p ∧ Prime (p + 2)}
- Twin count: π₂(N) = |{p ∈ T : p ≤ N}|
- Residue class: For m : ℕ, define (n mod m) as n % m

## Theorem (Twin Primes Mod 6 Structure)

For all twin primes p > 3: p ≡ 5 (mod 6), equivalently p ≡ -1 (mod 6).

Formally:
```
∀ p : ℕ, p > 3 → Prime p → Prime (p + 2) → p % 6 = 5
```

## Proof Sketch

**Step 1 (Primes > 3 are coprime to 6):**
All primes p > 3 satisfy gcd(p, 6) = 1.
Since 6 = 2 × 3, and p > 3 is prime, p is not divisible by 2 or 3.

**Step 2 (Residues coprime to 6):**
The residues coprime to 6 are: {1, 5} (mod 6).
- 0 ≡ 0 (mod 6) → divisible by 6
- 2 ≡ 2 (mod 6) → divisible by 2
- 3 ≡ 3 (mod 6) → divisible by 3
- 4 ≡ 4 (mod 6) → divisible by 2

So primes > 3 satisfy p ≡ 1 or p ≡ 5 (mod 6).

**Step 3 (Twin constraint eliminates p ≡ 1):**
If p ≡ 1 (mod 6), then:
- p + 2 ≡ 1 + 2 ≡ 3 (mod 6)
- p + 2 is divisible by 3
- Since p + 2 > 3, it cannot be prime

**Step 4 (Only p ≡ 5 remains):**
If p ≡ 5 (mod 6), then:
- p + 2 ≡ 5 + 2 ≡ 7 ≡ 1 (mod 6)
- p + 2 is coprime to 6
- p + 2 CAN be prime

Therefore, all twin primes p > 3 satisfy p ≡ 5 (mod 6).

## Key Lemmas Needed

1. **Prime coprimality:** For prime p > 3: gcd(p, 6) = 1
2. **Residue classification:** n coprime to 6 ↔ n ≡ 1 or n ≡ 5 (mod 6)
3. **Divisibility by 3:** If n ≡ 3 (mod 6) and n > 3, then n is composite
4. **Twin prime structure:** (p, p+2) twin with p > 3 → p ≡ 5 (mod 6)

## Lean Formalization Notes

The theorem signature in Lean 4 with Mathlib:

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq

theorem twin_prime_mod6 (p : ℕ) (hp3 : p > 3)
    (hp : Nat.Prime p) (hq : Nat.Prime (p + 2)) :
    p % 6 = 5 := by
  sorry
```

Required Mathlib lemmas:
- Nat.Prime.coprime_iff_not_dvd
- Nat.mod_mod_of_dvd
- Nat.Prime.eq_one_or_self_of_dvd
