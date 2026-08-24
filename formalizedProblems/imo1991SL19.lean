/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.NumberTheory.Niven
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 1991 #19
Let α ∈ ℚ with 0 < α < 1 and cos(3πα) + 2cos(2πα) = 0. prove α = 2/3
-/

namespace imo1991sl19
open Real
determine solution_set: Set (ℝ):= {2/3}

theorem imo1991_sl19 (a:ℝ)(ha: ¬Irrational a)(hal: 0 < a)(hau: a < 1)(hca: Real.cos (3 * Real.pi * a) + 2*Real.cos (2 * Real.pi *a) = 0): a ∈ solution_set := by
  let b := Real.pi * a
  have hb: 0 < b := by positivity
  have hbu : b < Real.pi := by
    unfold b
    nth_rw 2 [← mul_one Real.pi]
    rw [mul_lt_mul_iff_of_pos_left]
    lia
    positivity
  rw [show 3 * Real.pi * a = 3 * b by dsimp [b]; ring_nf] at hca
  rw [show 2 * Real.pi * a = 2 * b by dsimp [b]; ring_nf] at hca
  rw [Real.cos_three_mul, Real.cos_two_mul] at hca
  let x := Real.cos b
  ring_nf at hca
  rw [show -2 - x * 3 + x ^ 2 * 4 + x ^ 3 * 4  = (2*x+1)*(2*x^2+1*x + -2) by ring_nf] at hca
  have hroots : x = - (1/2) ∨ x = (-1 + Real.sqrt (17))/4 := by
    rw [mul_eq_zero] at hca
    rcases hca with lin | q
    left
    rw [add_eq_zero_iff_eq_neg] at lin
    apply_fun (·/2) at lin
    rw [mul_comm, mul_div_assoc, div_self, mul_one, neg_div] at lin
    assumption
    grind
    right
    rw [pow_two] at q
    have disc : discrim 2 1 (-2) = Real.sqrt 17 * Real.sqrt 17 := by
      unfold discrim
      simp
      ring_nf
    rw[ quadratic_eq_zero_iff (by grind: (2:ℝ)≠0) disc x] at q
    rcases q with l | r
    norm_num at l
    assumption
    norm_num at r
    unfold x at r
    have := Real.neg_one_le_cos b
    rw [r, neg_sub_left, neg_div, neg_le_neg_iff] at this
    have i1 : 5/4 ≤ ((sqrt 17) + 1)/4 := by
      rw [div_le_div_iff_of_pos_right (by positivity: (0:ℝ) < 4)]
      rw [show 5 = sqrt 16 + 1 by norm_num, add_le_add_iff_right, sqrt_le_sqrt_iff (by positivity : (0:ℝ) ≤ 17)]
      linarith
    have i2 := LE.le.trans i1 this
    linarith
  rcases hroots with l | r
  simp
  unfold x at l
  symm at l
  rw [neg_eq_iff_eq_neg] at l
  have hl2 := l
  rw [←Real.cos_add_pi] at l
  have h3 := Real.cos_pi_div_three
  have h2 := h3
  rw [l, cos_eq_cos_iff] at h2
  obtain ⟨k, hk⟩ := h2
  rcases hk with pos | neg
  have hk0 : (0:ℝ) < k := by
    have hb1: Real.pi < b + Real.pi := by linarith
    rw [pos,← sub_lt_iff_lt_add] at hb1
    rw [show π - π/3 = 2*π/3 by ring_nf] at hb1
    ring_nf at hb1
    rw [mul_assoc, mul_lt_mul_iff_of_pos_left, div_eq_mul_inv, mul_comm, mul_lt_mul_iff_of_pos_right] at hb1
    positivity
    positivity
    positivity
  unfold b at pos
  rw [show π * a + π = π * (a+1) by ring] at pos
  rw [show (2* ↑k * Real.pi) + Real.pi/3 = Real.pi * (2*↑k+1/3) by ring] at pos
  rw [mul_left_cancel_iff_of_pos pi_pos] at pos
  rw [show a + 1 = a + (3/3) by ring] at pos
  apply_fun (· - 1/3) at pos
  rw [add_sub_assoc, add_sub_assoc, sub_self, ← sub_div] at pos
  simp at pos
  norm_num at pos
  have k1: (1/3:ℝ )< ↑k := by linarith
  have k2: ↑k < (4/3:ℝ) := by linarith
  have k2a : k < (2:ℝ) := by linarith
  norm_cast at hk0 k2a
  have : k = 1 := by grind
  rw [this] at pos
  norm_num at pos
  field_simp at pos
  ring_nf at pos
  symm at pos
  apply sub_eq_of_eq_add' at pos
  norm_num at pos
  symm at pos
  rw [← div_eq_iff_mul_eq] at pos
  linarith
  norm_num
  have hk0 : (0:ℝ) < k := by
    have hb1: Real.pi < b + Real.pi := by linarith
    rw [neg, lt_sub_iff_add_lt] at hb1
    rw [show π + π/3 = 4*π/3 by ring_nf] at hb1
    ring_nf at hb1
    rw [mul_assoc, mul_lt_mul_iff_of_pos_left] at hb1
    linarith
    positivity
  unfold b at neg
  rw [show π * a + π = π * (a+1) by ring, show 2 * ↑k * π - π / 3 = π * (2 * ↑k - (1/3)) by ring,] at neg
  rw [mul_left_cancel_iff_of_pos pi_pos] at neg
  rw [show a + 1 = a + (3/3) by ring] at neg
  apply_fun (· + 1/3) at neg
  rw [sub_add, sub_self, sub_zero, add_assoc] at neg
  rw [show ((3:ℝ)/3) + (1/3) = 4/3 by ring_nf] at neg
  have hk2 : ↑k < (2:ℝ) := by linarith
  norm_cast at hk0 hk2
  have hk : k = 1 := by linarith
  rw [hk] at neg
  norm_num at neg
  rw [show (2:ℝ) = 6/3 by ring] at neg
  symm at neg
  apply sub_eq_of_eq_add at neg
  norm_num at neg
  symm
  assumption

  unfold x at r
  have hsin : sin b = √((-1 + √17) / 8) := by
    symm at r
    apply arccos_eq_of_eq_cos at r
    apply congrArg sin at r
    rw [sin_arccos] at r
    ring_nf at r
    field_simp at r
    norm_num at r
    ring_nf at r
    field_simp at r
    symm at r
    rw [mul_comm] at r
    apply eq_div_of_mul_eq at r
    norm_num at r
    rw [show (128:ℝ) = 16 * 8 by norm_num, sqrt_mul] at r
    norm_num at r
    rw [mul_div_mul_comm, div_self, one_mul, ← sqrt_div] at r
    assumption
    any_goals simp
    linarith
    linarith

  have ⟨q, hq⟩ := exists_rat_of_not_irrational ha
  have hst : ∃s:ℤ, ∃t:ℕ, q = ↑s/↑t ∧ t≠0 := by
    use q.num, q.den
    norm_cast
    simp
  obtain ⟨s,t,hdv, tnz⟩ := hst
  unfold b at r hsin
  rw [hq, hdv] at r hsin
  push_cast at r hsin
  sorry





end imo1991sl19
