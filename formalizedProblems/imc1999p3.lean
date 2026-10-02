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
## IMC 1999 p3
https://www.imc-math.org.uk/imc1999/prob_sol1.pdf
-/
namespace imc1999
open Finset

theorem imc1999p3 {f:ℝ→ℝ}(h: ∀x y, ∀m:ℕ, 0 < m→ |∑ k ∈ Icc 0 m, 3^k * (f (x+k*y) - f (x-k*y))| ≤ 1): ∃c, ∀x, f x = c := by
  have term_le: ∀x y:ℝ, ∀n:ℕ, 0 < n → |f (x + ↑n * y) - f (x - ↑n * y)| ≤ 2 / 3 ^ n := by
    intro x y n hn
    have h1 := h x y n hn
    have h' := h1
    rw [← insert_Icc_sub_one_right_eq_Icc, sum_insert] at h1
    change |3 ^ n * (f (x + ↑n * y) - f (x - ↑n * y)) + ∑ k ∈ Icc 0 (n - 1), 3 ^ k * (f (x + k * y) - f (x - k * y))| ≤ 1 at h1
    let sum_0 := ∑ k ∈ Icc 0 n, 3 ^ k * (f (x + ↑k * y) - f (x - ↑k * y))
    let sum_1 := ∑ k ∈ Icc 0 (n - 1), 3 ^ k * (f (x + ↑k * y) - f (x - ↑k * y))
    change |sum_0| ≤ 1 at h'
    change |3 ^ n * (f (x + ↑n * y) - f (x - ↑n * y)) + sum_1| ≤ 1 at h1
    have e1: 3 ^ n * (f (x + ↑n * y) - f (x - ↑n * y)) = sum_0 - sum_1 := by
      have v1: ∑ k ∈ Icc 0 n, 3 ^ k * (f (x + ↑k * y) - f (x - ↑k * y)) = sum_0 := by rfl
      rw [← insert_Icc_sub_one_right_eq_Icc, sum_insert] at v1
      change 3 ^ n * (f (x + ↑n * y) - f (x - ↑n * y)) + sum_1 = sum_0 at v1
      rw [← eq_sub_iff_add_eq] at v1
      assumption
      simp; lia; lia

    have i1: |sum_0 - sum_1| ≤ 2 := by
      have i2:= abs_sub sum_0 sum_1
      trans |sum_0| + |sum_1|
      assumption
      suffices i3: |sum_1| ≤ 1
      linarith
      by_cases! hn': n ≤ 1
      have hn'': n = 1 := by grind
      unfold sum_1
      rw [hn'']
      norm_num
      exact h x y (n-1) (by lia)

    rw [← e1, abs_mul, abs_pow, mul_comm] at i1
    norm_num at i1
    rwa [← le_div_iff₀] at i1
    positivity; simp; lia;lia


  have fconst: ∀u v, f u = f v := by
    intro u v
    by_contra! hf
    have ⟨m, hm⟩:= exists_pow_lt_of_lt_one (by positivity: 0 < |f u - f v|) (by linarith: (1:ℝ) > 1/3)
    let n := m + 1
    have npos: 0 < n := by
      unfold n
      linarith
    have hn': 2 * (1 / 3) ^ n < |f u - f v| := by
      unfold n
      rw [pow_succ', ← mul_assoc]
      norm_num
      trans (1/3)^m
      field_simp; norm_num
      assumption
    rw [one_div_pow, mul_one_div] at hn'
    have ⟨x, y, hx, hy⟩: ∃x y, x - n*y = u ∧ x + n*y = v := by
      use ((u+v)/2), ((v-u)/(2*n))
      field_simp
      ring_nf
      simp
    specialize term_le x y n npos
    rw [hx, hy, abs_sub_comm] at term_le
    linarith
  use f 2
  intro x
  exact fconst x 2


end imc1999
