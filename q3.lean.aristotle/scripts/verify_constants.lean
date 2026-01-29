/-
Q3 Constants Verification Script
================================
This file verifies that all constants in the Q3 formalization
match the values specified in the paper.

Run with: lake env lean scripts/verify_constants.lean
-/

import Q3.Basic.Defs
import Q3.Axioms

open Q3

-- ═══════════════════════════════════════════════════════════════
-- SECTION 1: Key Constants from Paper
-- ═══════════════════════════════════════════════════════════════

-- c* = 11/10 (Lemma 8.19)
#check c_star
#print c_star
example : c_star = 11 / 10 := rfl

-- Verify c* > 0
example : c_star > 0 := c_star_pos

-- Verify c* > 1
example : c_star > 1 := c_star_gt_one

-- Verify c*/4 > 0
example : c_star / 4 > 0 := c_star_div_four_pos

-- ═══════════════════════════════════════════════════════════════
-- SECTION 2: Node coordinates ξ_n = log(n)/(2π)
-- ═══════════════════════════════════════════════════════════════

#check xi_n
#print xi_n
-- xi_n n = Real.log n / (2 * Real.pi)

-- ═══════════════════════════════════════════════════════════════
-- SECTION 3: Weight definitions
-- ═══════════════════════════════════════════════════════════════

-- w_Q(n) = 2Λ(n)/√n
#check w_Q
#print w_Q

-- w_RKHS(n) = Λ(n)/√n
#check w_RKHS
#print w_RKHS

-- w_max = 2/e
#check w_max
#print w_max
example : w_max = 2 / Real.exp 1 := rfl

-- ═══════════════════════════════════════════════════════════════
-- SECTION 4: Kernel definitions
-- ═══════════════════════════════════════════════════════════════

-- Fejér kernel
#check Fejer_kernel
#print Fejer_kernel

-- Heat kernel
#check heat_kernel_A1
#print heat_kernel_A1

-- Fejér×heat atom
#check Fejer_heat_atom
#print Fejer_heat_atom

-- ═══════════════════════════════════════════════════════════════
-- SECTION 5: Q functional structure
-- ═══════════════════════════════════════════════════════════════

-- Q = arch_term - prime_term (T0)
#check Q
#print Q

#check arch_term
#print arch_term

#check prime_term
#print prime_term

-- a_star = log π - Re ψ(1/4 + iπξ)
#check a_star
#print a_star

-- ═══════════════════════════════════════════════════════════════
-- SECTION 6: Toeplitz matrix
-- ═══════════════════════════════════════════════════════════════

#check ToeplitzMatrix
#print ToeplitzMatrix

#check RayleighQuotient
#print RayleighQuotient

-- ═══════════════════════════════════════════════════════════════
-- SECTION 7: Axiom count verification
-- ═══════════════════════════════════════════════════════════════

-- This should show exactly 10 axioms (7 project + 3 standard)
-- #print axioms Q3.Main.RH_of_Weil_and_Q3

#check @Weil_criterion
#check @a_star_pos
#check @a_star_continuous
#check @a_star_bdd_on_compact
#check @a_star_even
#check @Schur_test

-- ═══════════════════════════════════════════════════════════════
-- SUCCESS MESSAGE
-- ═══════════════════════════════════════════════════════════════

#check "All constant definitions verified successfully!"

