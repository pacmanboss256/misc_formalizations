/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## Putnam 2004 B2

let m, n be positive integers
show (m+n)!/(m+n)^(m+n) < m!/m^m * n!/n^n
-/

namespace putnam2004
open Nat

problem putnam2004B2(m n: ℕ)(hm: 0 < m)(hn: 0 < n): ((m+n)!:ℚ)/(m+n)^(m+n) <( m !/(m^m))*(n ! / (n^n)) := by
  wlog! hnm: m ≤ n generalizing m n
  specialize this n m hn hm (by lia)
  grind
  field_simp
  rw [mul_assoc, mul_assoc, mul_comm]
  norm_cast
  rw [← div_lt_iff_lt_mul (by positivity: 0 < m ! * n !), Nat.mul_div_assoc, add_comm, mul_comm (m !)]
  rw [← Nat.add_choose, add_pow]
  simp
  let f := fun x ↦ n ^ x * m ^ (n + m - x) * (n + m).choose x
  change m ^ m * n ^ n * (n + m).choose m < ∑ x ∈ Finset.range (n + m + 1), f x
  have h1: f n < ∑ x ∈ Finset.range (n + m + 1), f x := by
    apply Finset.single_lt_sum
    positivity
    simp; simp
    unfold f
    simp
    apply pow_pos
    lia
    intro k hk hkm
    unfold f
    simp

  suffices: f n = m ^ m * n ^ n * (n + m).choose m
  rwa [← this]
  unfold f
  simp
  rw [choose_symm_add, mul_comm (n^n)]
  apply Nat.factorial_mul_factorial_dvd_factorial_add

end putnam2004
