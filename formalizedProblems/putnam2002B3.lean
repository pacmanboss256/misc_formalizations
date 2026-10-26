/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## Putnam 2002 B3
Show for all n > 1, 1/2ne < 1/e - (1-1/n)^n < 1/ne
-/
namespace putnam2002
open Real

noncomputable def e := exp 1

theorem hleft(n:ℕ)(hn: n > 1): 1/(2*n*e) < 1/e - (1-(1/n))^n := by
  rw [← mul_lt_mul_iff_of_pos_left (by exact Real.exp_pos 1: 0 < e)]
  rw [← mul_div_assoc, mul_div_right_comm, ← mul_rotate, div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div]
  rw [div_self (by unfold e; positivity), mul_one, one_mul, mul_sub, mul_one_div e, div_self (by unfold e; positivity)]
  rw [lt_sub_iff_add_lt', ← lt_sub_iff_add_lt, mul_one_div, div_div]
  have p1: 0 < e * (1 - 1 / ↑n) ^ n := by
    unfold e
    rw [mul_pos_iff_of_pos_left (by positivity)]
    apply pow_pos
    simp
    have h1: (n:ℝ)⁻¹ ≤ 1 := by apply Nat.cast_inv_le_one
    apply lt_or_eq_of_le at h1
    rcases h1 with h | h
    assumption
    simp at h
    lia
  rw [← exp_log p1, log_mul, log_pow, ← log_lt_log_iff, log_exp]
  unfold e
  rw [log_exp, ← neg_lt_neg_iff, neg_add, neg_add_eq_sub, ← neg_mul]
  have ipos: |(1:ℝ)/(2*n)|<1 := by
    simp
    field_simp
    norm_cast; lia
  have hlog:= (HasSum.tsum_eq (Real.hasSum_pow_div_log_of_abs_lt_one ipos)).symm
  have hlog2 :=(HasSum.tsum_eq (Real.hasSum_pow_div_log_of_abs_lt_one (by simp; field_simp; norm_cast: |(1:ℝ)/n|<1))).symm
  apply_fun ((n:ℝ)*·) at hlog2
  rw [mul_neg, ← neg_mul, ← tsum_mul_left, Summable.tsum_eq_zero_add] at hlog2
  push_cast at hlog2
  rw [zero_add, pow_one, div_one, mul_one_div, div_self] at hlog2
  rw [hlog, hlog2, add_sub_cancel_left]
  apply Summable.tsum_lt_tsum
  intro w
  ring_nf
  field_simp
  rw [mul_add, show (1 / 2) ^ w * (w:ℝ) = ((1/2)^(w+1) * (w:ℝ))*2 by ring_nf, ← add_mul]
  field_simp
  rw [← mul_one ((1 / 2) ^ w), pow_succ, mul_assoc, ← mul_add, one_div_pow]
  field_simp
  trans 2*(1+w)
  linarith; field_simp
  norm_cast
  apply Nat.one_le_two_pow
  field_simp
  simp
  field_simp
  ring_nf
  field_simp
  rw [← mul_pow, mul_one_div_cancel]
  simp
  field_simp
  norm_cast
  trans 2 * (1 + n); linarith
  rw [mul_assoc]
  simp; lia; norm_cast; lia
  exact HasSum.summable (Real.hasSum_pow_div_log_of_abs_lt_one ipos)
  apply Summable.mul_left

  have hl2:= HasSum.summable (Real.hasSum_pow_div_log_of_abs_lt_one (by simp; field_simp; norm_cast: |(1:ℝ)/n|<1))
  norm_cast
  let f:= fun (i:ℕ) ↦ (1 / (n:ℝ)) ^ (i + 1) / (i + 1)
  have f1: (fun (i:ℕ) ↦ ((1 / (n:ℝ)) ^ (i + 1 + 1) / ↑(i + 1 + 1))) = fun i ↦ f (i+1) := by
    funext w
    unfold f
    norm_cast
  rw [f1, summable_nat_add_iff 1]
  unfold f
  assumption
  norm_cast; positivity
  use (-↑n * log (1 - 1 / ↑n))
  symm at hlog2
  rwa [← Summable.hasSum_iff] at hlog2
  have hl2:= HasSum.summable (Real.hasSum_pow_div_log_of_abs_lt_one (by simp; field_simp; norm_cast: |(1:ℝ)/n|<1))
  apply Summable.mul_left; assumption
  positivity
  field_simp
  simp; norm_cast; lia
  unfold e; positivity
  apply pow_ne_zero; field_simp
  apply div_ne_zero
  rw [sub_ne_zero]
  norm_num; lia; norm_cast; positivity

theorem hright(n:ℕ)(hn: n > 1):1/e - (1-(1/n))^n < 1/(n*e):= by
  rw [← mul_lt_mul_iff_of_pos_left (by exact Real.exp_pos 1: 0 < e),mul_sub,mul_one_div_cancel (by unfold e; positivity)]
  rw [mul_one_div, mul_comm _ e, div_mul_eq_div_mul_one_div, div_self (by unfold e; positivity), one_mul, sub_lt_iff_lt_add']
  rw [← sub_lt_iff_lt_add]
  have p1: 0 < e * (1 - 1 / ↑n) ^ n := by
    unfold e
    rw [mul_pos_iff_of_pos_left (by positivity)]
    apply pow_pos
    simp
    have h1: (n:ℝ)⁻¹ ≤ 1 := by apply Nat.cast_inv_le_one
    apply lt_or_eq_of_le at h1
    rcases h1 with h | h
    assumption
    simp at h
    lia
  rw [← exp_log p1, log_mul, log_pow, ← log_lt_log_iff, log_exp]
  unfold e
  rw [log_exp, ← neg_lt_neg_iff, neg_add, neg_add_eq_sub, ←mul_neg]
  have ipos: |1/(n:ℝ)|<1 := by
    simp; field_simp; norm_cast
  have hl:= (Real.hasSum_pow_div_log_of_abs_lt_one ipos)
  have hlog := HasSum.tsum_eq hl
  rw [← hlog]
  nth_rw 1 [Summable.tsum_eq_zero_add (HasSum.summable hl)]
  rw [mul_add, ← tsum_mul_left, zero_add, pow_one]
  norm_cast
  rw [zero_add]
  norm_cast
  rw [div_one, mul_one_div_cancel (by norm_cast; positivity), add_sub_cancel_left]
  apply Summable.tsum_lt_tsum
  intro w; simp;field_simp; norm_cast; ring_nf; simp
  apply Nat.le_mul_of_pos_right; decide
  field_simp; simp; ring_nf; field_simp; norm_cast; lia
  let f:= fun (i:ℕ) ↦ (1 / (n:ℝ)) ^ (i + 1) / (i + 1)
  have f1: (fun (i:ℕ) ↦ ((1 / (n:ℝ)) ^ (i + 1 + 1) / ↑(i + 1 + 1))) = fun i ↦ f (i+1) := by
    funext w
    unfold f
    norm_cast
  apply Summable.mul_left
  rw [f1, summable_nat_add_iff 1]
  unfold f; exact (HasSum.summable hl)
  exact_mod_cast (HasSum.summable hl)
  field_simp; simp; assumption
  positivity; unfold e; positivity
  rw [pow_ne_zero_iff, sub_ne_zero]
  simp; lia; lia







problem putnam2002B3: ∀n:ℕ, n > 1 → 1/(2*n*e) < 1/e - (1-(1/n))^n ∧ 1/e - (1-(1/n))^n < 1/(n*e):= by
  intro n hn
  constructor
  exact hleft n hn
  exact hright n hn



end putnam2002
