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
## Putnam 1957 A3
show |(cos(kb)cos(a)-cos(ka)cos(b)/(cos(b)-cos(a))| < k^2-1

for all real a,b and int k whenever defined
-/

namespace putnam1957
open Real
lemma hsin: ∀x, sin x ≠ 0 → ∀k:ℤ, 2≤ k → |sin (k*x)| < k*|sin x| := by
  intro z hz k hk
  induction k, hk using Int.leInduction with
  | base =>
      norm_cast
      rw [sin_two_mul]
      simp; field_simp
      suffices: |cos z| ≠ 1
      have hbound:= abs_cos_le_one z
      rw [lt_iff_le_and_ne]
      exact ⟨hbound, this⟩
      contrapose hz
      rw [show (1:ℝ) = |1| by norm_num, abs_eq_abs] at hz
      rwa [sin_eq_zero_iff_cos_eq]
  | succ k hk ih  =>
    push_cast
    rw [add_mul, add_mul, sin_add]
    simp
    have i1:= abs_add_le (sin (↑k * z) * cos z) (cos (↑k * z) * sin z)
    apply LE.le.trans_lt i1
    simp
    have i2: |sin (↑k * z)| * |cos z| + |cos (↑k * z)| * |sin z| ≤ |sin (↑k * z)| + |sin z| := by
      apply add_le_add
      have i2':= abs_cos_le_one z
      nth_rw 2 [← mul_one |sin (↑k * z)|]
      apply mul_le_mul; rfl; assumption
      positivity; positivity
      have i2':= abs_cos_le_one (k*z)
      nth_rw 2 [← one_mul |sin (z)|]
      apply mul_le_mul; assumption; rfl
      positivity; positivity
    apply LE.le.trans_lt i2
    rwa [add_lt_add_iff_right]


problem putnam1957A3(a b:ℝ)(k:ℤ)(kpos: 1 < k)(hdef: cos b ≠ cos a): |(cos (k*b)*(cos a) - (cos (k*a)*(cos b)))/(cos b - cos a)| < k^2 - 1 := by
  rw [← one_mul ((cos (↑k * b) * cos a - cos (↑k * a) * cos b) / (cos b - cos a))]
  nth_rw 1 [show (1:ℝ) = 2/2 by simp]
  rw [div_mul_div_comm, abs_div]
  field_simp
  rw [mul_sub, ← mul_assoc, ← mul_assoc, two_mul_cos_mul_cos,two_mul_cos_mul_cos]
  have ⟨x,y,hx,hy⟩: ∃x y, a = x+y ∧ b = x-y := by
    use (a+b)/2, (a-b)/2
    ring_nf; simp
  rw [hx, hy, show  k * (x + y) - (x-y) = (k-1)*x+(k+1)*y by ring_nf]
  rw [show k * (x - y) + (x+y) = (k+1)*x-(k-1)*y by ring_nf]
  rw [show k * (x - y) - (x+y) = (k-1)*x-(k+1)*y by ring_nf]
  rw [show k * (x + y) + (x-y) = (k+1)*x+(k-1)*y by ring_nf]
  have e1: cos ((↑k - 1) * x - (↑k + 1) * y) + cos ((↑k + 1) * x - (↑k - 1) * y) -
      (cos ((↑k - 1) * x + (↑k + 1) * y) + cos ((↑k + 1) * x + (↑k - 1) * y)) =
      2*(sin ((k+1)*x) * sin ((k-1)*y) + sin ((k-1)*x)*sin ( (k+1)*y)) := by

    rw [sub_add_eq_sub_sub,add_sub_right_comm,←two_mul_sin_mul_sin, add_sub_assoc,← two_mul_sin_mul_sin, mul_add]
    rw [add_comm (2 * (sin ((↑k + 1) * x) * sin ((↑k - 1) * y))), mul_assoc, mul_assoc]

  rw [e1]
  clear e1
  rw [abs_mul, abs_mul]; field_simp
  rw [← two_mul_sin_mul_sin]
  have hsz: sin x ≠ 0 ∧ sin y ≠ 0 := by
    rw [hx, hy] at hdef
    contrapose hdef
    rw [not_and_or] at hdef
    push Not at hdef
    rw [cos_sub, cos_add, sub_eq_add_neg, add_left_cancel_iff]
    rcases hdef with h | h <;> rw [h]<;> simp


  obtain ⟨hxnz, hynz⟩:= hsz
  by_cases hk2: k = 2
  rw [hk2]; norm_num
  rw [sin_three_mul, sin_three_mul]
  ring_nf
  field_simp; simp; field_simp
  rw [mul_comm _ 4, sub_sub, ← mul_add,abs_sub_lt_iff]
  constructor; simp; positivity
  rw [← add_lt_add_iff_right 6,sub_add_cancel]
  norm_num; rw [show (12:ℝ) = 4*3 by ring]; field_simp
  have hs1: sin y ^ 2 + sin x ^ 2 ≤ 1+1 := by
    apply add_le_add <;> simp <;> apply abs_sin_le_one
  apply LE.le.trans_lt hs1
  norm_num

  have hk: 3 ≤ k := by lia
  rw [mul_comm x _]
  have hsxa:= hsin x hxnz (k-1) (by lia)
  have hsxb:= hsin x hxnz (k+1) (by lia)
  have hsya:= hsin y hynz (k-1) (by lia)
  have hsyb:= hsin y hynz (k+1) (by lia)
  have i1 := abs_add_le (sin ((↑k + 1) * x) * sin ((↑k - 1) * y)) (sin ((↑k - 1) * x) * sin ((↑k + 1) * y))
  apply LE.le.trans_lt i1
  clear i1
  have i2: |sin ((↑k + 1) * x) * sin ((↑k - 1) * y)| + |sin ((↑k - 1) * x) * sin ((↑k + 1) * y)| < (↑(k + 1) * |sin x|) * (↑(k - 1) * |sin y|) + (↑(k - 1) * |sin x|) * (↑(k + 1) * |sin y|):= by
    apply add_lt_add
    simp; apply mul_lt_mul'
    apply le_of_lt; exact_mod_cast hsxb
    exact_mod_cast hsya; positivity
    positivity
    simp; apply mul_lt_mul'
    apply le_of_lt; exact_mod_cast hsxa
    exact_mod_cast hsyb; positivity
    rw [mul_pos_iff]; left
    constructor
    norm_num; norm_cast; lia
    simp; assumption

  apply LT.lt.trans_le i2
  clear i2
  move_mul [← |sin x|, ← |sin y|]
  push_cast
  rw [mul_assoc, mul_assoc _ ((k:ℝ)-1) (k+1), ← mul_add]
  simp; field_simp
  ring_nf; rfl


end putnam1957
