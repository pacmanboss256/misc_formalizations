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
## IMO Shortlist 1999 A5
Find all functions f : ℝ → ℝ such that
f(x-f(y))=f(f(y))+xf(y)+f(x)-1 for all x,y ∈ ℝ
-/

namespace imo1999A5
open Real

determine solution_set: Set (ℝ→ℝ) := {fun x ↦ 1 - (x^2)/2}

theorem imo1999SLA5(f:ℝ→ℝ): f ∈ solution_set ↔ ∀x y, f (x - f y) = f (f y) + x * (f y) + f x - 1 := by
  constructor
  · intro h x y
    simp at h
    simp [h]
    ring_nf
  intro h
  have fz_nz : f 0 ≠ 0 := by
    by_contra! hfz
    specialize h 0 0
    rw [hfz] at h
    simp at h
    rw [hfz] at h
    simp at h
  have fsurj : ∀x, ∃u v, f u - f v = x := by
    intro x
    specialize h ((x - f (f 0) + 1)/(f 0)) 0
    field_simp at h
    have lhs : f (f 0) + (x - f (f 0) + 1) + f ((x - f (f 0) + 1) / f 0) - 1 = x + f ((x - f (f 0) + 1) / f 0) := by ring_nf
    rw [lhs] at h
    clear lhs
    apply sub_eq_of_eq_add at h
    let u := (x - f (f 0) + 1 - f 0 ^ 2) / f 0
    let v := (x - f (f 0) + 1) / f 0
    change f u - f v = x at h
    use u, v
  have h1 : ∀x, f (f x) = (f 0 + 1 - f x ^ 2) / 2 := by
    intro x
    specialize h (f x) x
    simp at h
    rw [add_comm, ← add_assoc, ← two_mul, ← pow_two, add_sub_assoc] at h
    apply sub_eq_of_eq_add at h
    symm at h
    rw [sub_sub_eq_add_sub] at h
    apply_fun (· / 2) at h
    rw [mul_comm, mul_div_assoc, div_self, mul_one] at h
    · assumption
    simp

  have hf: ∀x, f x = f 0 - (x^2) / 2 := by
    intro x
    choose u v ht using fsurj x
    have huv := h (f u) v
    have hft := h1 x
    rw [h1, h1] at huv
    ring_nf at huv
    field_simp at huv
    rw [mul_add, ← mul_assoc, mul_neg, ← pow_two, ← sub_eq_add_neg, ←sub_eq_add_neg] at huv
    rw [show f u * f v * 2 - f u ^ 2 - f v ^ 2 + 2 * f 0 = 2 * f 0 - (f u ^ 2 - 2 * f u * f v + f v ^ 2) by ring_nf] at huv
    rw [← sub_sq] at huv
    apply_fun (· / 2) at huv
    rw [mul_div_assoc, sub_div] at huv
    simp at huv
    rw [← ht]
    assumption

  have f1: f 0 = 1 := by
    specialize h1 0
    specialize hf (f 0)
    rw [h1] at hf
    field_simp at hf
    ring_nf at hf
    apply_fun (·+ (f 0)^2) at hf
    rw [sub_add_cancel, sub_add_cancel, mul_two, add_right_cancel_iff] at hf
    symm
    assumption
  rw [f1] at hf
  simp
  funext w
  specialize hf w
  assumption

end imo1999A5
