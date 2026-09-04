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
## IMO Shortlist 2005 A4
Find all functions f: ℝ → ℝ such that
f(x+y)+f(x)f(y) =f(xy) + 2xy + 1
-/

namespace imo2004a6
open Real
determine solution_set : Set (ℝ→ℝ) := {fun x ↦ 2*x - 1, fun x ↦ x^2 - 1, fun x ↦ -x-1}

snip begin
lemma sub_eq_sub_of_eq{a b c d:ℝ}(h1: a = b)(h2: c = d): a - c = b - d := by
      rw [h1, h2]
lemma f0(f: ℝ→ℝ)(h: ∀x y:ℝ, f (x+y) + (f x) * (f y) = f (x*y) + 2*x*y+1): f 0 = -1 := by
  have f0 := h 0 0
  simp at f0
  rw [← pow_two, sq_eq_one_iff] at f0
  rcases f0 with pos | neg
  · have f1: ∀x, f x = 1 := by
      intro x
      have hx:= h x 0
      simp [pos, ← two_mul] at hx
      assumption
    have f3 := h 3 3
    norm_num at f3
    simp [f1] at f3
  assumption

lemma f11(f:ℝ→ℝ)(h: ∀x y:ℝ, f (x+y) + (f x) * (f y) = f (x*y) + 2*x*y+1)(f1: f 1 = 1): ∀x, f x = 2*x - 1 := by
  intro x
  have fx1:= h x 1
  ring_nf at fx1
  simp [f1] at fx1
  have fx0 := h (x-1) 1
  simp [f1] at fx0
  rw [add_comm, add_assoc, add_left_cancel_iff, mul_sub] at fx0
  simp at fx0
  ring_nf at fx0
  rw [add_comm, mul_comm, ← sub_eq_add_neg] at fx0
  assumption


lemma fn10(f:ℝ→ℝ)(h: ∀x y:ℝ, f (x+y) + (f x) * (f y) = f (x*y) + 2*x*y+1)(fn1: f (-1) = 0)(f1: f 1 = 0):
  ∀x, f x = x^2 - 1 := by
    have f_even: ∀y, f y = f (-y) := by
      intro y
      have ⟨x, hx⟩: ∃x, y = x-1 := by
        use y+1
        simp
      have fx1 := h x (-1)
      have f1x := h (-x) 1
      simp at fx1 f1x
      rw [← fx1] at f1x
      simp [f1, fn1] at f1x
      rw [← sub_eq_add_neg, show -x + 1 = -(x-1) by ring] at f1x
      symm
      rwa [hx]
    have fsq:∀y, f y = y^2 - 1 := by
      intro y
      have ⟨x, hx⟩: ∃x, y = x*2 := by
          use y/2
          ring
      have hxx := h x x
      have hxnx := h x (-x)
      have f0 := f0 f h
      simp [f0] at hxnx
      rw [← f_even, ← f_even, ← sub_eq_add_neg] at hxnx
      ring_nf at hxnx hxx
      symm at hxnx hxx
      apply sub_eq_of_eq_add' at hxnx
      simp at hxnx
      apply sub_eq_of_eq_add at hxx
      rw [←hxx] at hxnx
      ring_nf at hxnx
      rw [add_sub_right_comm, add_right_cancel_iff] at hxnx
      apply sub_eq_of_eq_add' at hxnx
      ring_nf at hxnx
      apply_fun (· * -1) at hxnx
      ring_nf at hxnx
      symm at hxnx
      rw [show x^2*4 = (x*2)^2 by ring, ← hx, add_comm, ← sub_eq_add_neg] at hxnx
      assumption
    apply fsq



lemma f12(f:ℝ→ℝ)(h: ∀x y:ℝ, f (x+y) + (f x) * (f y) = f (x*y) + 2*x*y+1)(fn1: f (-1) = 0)(f1: f 1 = -2): ∀x, f x = -x - 1 := by
  have f0 := f0 f h
  have fx1 : ∀x, f (x+1) = 3 * f x + 2*x + 1 := by
    intro x
    have hx1 := h x 1
    simp [f1] at hx1
    rw [← sub_eq_add_neg, sub_eq_iff_eq_add', ← add_assoc, ← add_assoc] at hx1
    ring_nf at hx1
    rw [add_comm, mul_comm, add_rotate, mul_comm]
    nth_rw 3 [add_comm]
    assumption
  have fnx : ∀x, f (-1 + x) = - f (-1 - x) := by
    have inter1: ∀x, f x - f (-x) = f (-1 + x) * 2 := by
      intro x
      have ⟨y, hx⟩: ∃y:ℝ, y = 1-x:= by
        use 1-x
      have h1nx := h 1 (-y)
      simp [f1] at h1nx
      ring_nf at h1nx
      rw [sub_eq_iff_eq_add'] at h1nx
      ring_nf at h1nx
      have hn1x := h (-1) y
      simp [fn1] at hn1x

      have hs1 := sub_eq_sub_of_eq h1nx hn1x
      ring_nf at hs1
      rw [show -1 + y = -(1-y) by ring_nf, hx] at hs1
      ring_nf at hs1
      assumption
    intro x
    have iy := inter1 x
    have iny := inter1 (-x)
    simp at iny
    apply_fun (· * -1) at iny
    simp at iny
    rw [iny, ← neg_mul, mul_right_cancel_iff_of_pos (by positivity)] at iy
    ring_nf at iy
    symm
    assumption
  have fevenoffset : ∀x, f x + f (-x) = -2 := by
    intro x
    have hx := h x (-1)
    have hnx := h (-x) (-1)
    simp [fn1] at hx hnx
    ring_nf at hnx hx
    rw [fnx x] at hx
    apply_fun (· * -1) at hx
    simp at hx
    rw[hnx] at hx
    ring_nf at hx
    rw [add_comm (-1) (x*2), add_comm 1 (x*2), add_assoc, add_sub_assoc, add_left_cancel_iff] at hx
    symm at hx
    apply eq_add_of_sub_eq at hx
    rw [add_rotate] at hx
    apply_fun (· -1) at hx
    norm_num at hx
    symm; assumption
  have f2x: ∀x, f (2*x) = 2* f x + 1 := by
    intro x
    have hxnx := h x (-x)
    simp [f0] at hxnx
    apply_fun (1+·) at hxnx
    norm_num at hxnx
    ring_nf at hxnx
    rw [sub_add_comm, mul_comm _ 2] at hxnx
    rw [← sub_eq_iff_eq_add'.mpr (fevenoffset x).symm, ← sub_eq_iff_eq_add'.mpr (fevenoffset (x^2)).symm] at hxnx
    rw [add_comm, ← add_sub_assoc, ← add_sub_assoc, add_neg_cancel] at hxnx
    apply_fun (·*-1) at hxnx
    ring_nf at hxnx
    have hxx := h x x
    ring_nf at hxx
    symm at hxx hxnx
    rw [← sub_eq_iff_eq_add'] at hxx hxnx
    rw [← hxnx, add_rotate, add_assoc, add_sub_assoc] at hxx
    nth_rw 2 [add_sub_assoc] at hxx
    rw [add_left_cancel_iff, add_sub_assoc, sub_eq_add_neg _ (f x * 2), add_left_cancel_iff, sub_eq_iff_eq_add', ← sub_eq_add_neg] at hxx
    symm at hxx
    rw [sub_eq_iff_eq_add', add_comm] at hxx
    ring_nf
    assumption

  have f2:= fx1 1
  simp [f1] at f2
  norm_num at f2
  have fx2 : ∀x, f (x+2) = 5*f x + 4*x + 2 := by
    intro x
    have hx2:= h x 2
    simp [f2] at hx2
    rw [mul_comm x 2, f2x x] at hx2
    ring_nf at hx2
    rw [sub_eq_iff_eq_add'] at hx2
    ring_nf at hx2
    ring_nf
    assumption
  intro x
  have hx0 := fx1 x
  rw [add_comm] at hx0
  have hx1 := fx1 (x+1)
  have hx2 := fx2 x
  ring_nf at hx1
  rw [add_comm, hx2,hx0] at hx1
  ring_nf at hx1
  apply sub_eq_zero_of_eq at hx1
  ring_nf at hx1
  apply_fun (·*-1) at hx1
  simp at hx1
  ring_nf at hx1
  rw [← eq_sub_iff_add_eq, zero_sub] at hx1
  apply_fun (·*-1/4) at hx1
  ring_nf at hx1
  rw [neg_sub_comm] at hx1
  symm
  assumption















snip end

theorem imo2004SLA6(f:ℝ→ℝ): f ∈ solution_set ↔ ∀x y:ℝ, f (x+y) + (f x) * (f y) = f (x*y) + 2*x*y+1 := by
  constructor
  · intro hf x y
    simp at hf
    rcases hf with h | h | h <;> simp [h] <;> ring_nf
  intro h
  have f0 := f0 f h
  have f1:= h 1 (-1)
  ring_nf at f1
  simp [f0] at f1
  rw [mul_left_eq_self₀] at f1
  rcases f1 with one | neg_zero
  · have f11 := f11 f h one
    simp
    left
    funext w
    exact f11 w
  have f1:= h (-1) (-1)
  simp [neg_zero] at f1
  ring_nf at f1
  have f2:= h 1 (-2)
  ring_nf at f2
  simp [neg_zero, f1] at f2
  rw [mul_right_eq_self₀] at f2
  symm at f2
  rcases f2  with f10 | f1n2
  · have h10 := fn10 f h neg_zero f10
    simp
    right
    left
    funext w
    exact h10 w
  symm at f1n2
  rw [← sub_eq_iff_eq_add'] at f1n2
  ring_nf at f1n2
  symm at f1n2
  have fnx1:= f12 f h neg_zero f1n2
  simp
  right; right
  funext w
  exact fnx1 w




end imo2004a6
