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
## IMO Shortlist 2009 A7
Find all functions f: ℝ → ℝ such that
f(x * f(x+y)) = f(y * f(x)) + x^2 for all x y ∈ ℝ
-/

namespace imo2009a7
open Real Function
determine solution_set: Set (ℝ→ℝ) := {fun a ↦ a, fun a ↦ -a}
snip begin
variable {f:ℝ→ℝ}(h: (∀x y, f (x*f (x+y)) = f (y* f x) + x^2))
include f h

lemma hf0: ∀x:ℝ, f x = 0 ↔ x = 0:= by
  intro x
  constructor
  · intro f0
    have h0 := h x 0
    simp [f0] at h0
    assumption
  intro xz
  by_cases! hfz: f 0 = 0
  · rwa [xz]
  have fc:∀x, f x = f 0 := by
    intro z
    have h1 := h 0 (z/ (f 0))
    by_contra! hf0
    simp at h1
    rw [div_mul_cancel₀ z hfz] at h1
    symm at h1
    contradiction
  have h2:= h 2 0
  simp at h2
  rw [fc] at h2
  norm_num at h2

lemma f0: f 0 = 0 := by simp [hf0 h]

lemma hinj: Injective f := by
  intro a b feq
  by_cases! abeq: a = b
  · assumption
  have hab:= h b (a-b)
  simp at hab
  have hb0 := h b 0
  simp [f0 h] at hb0
  rw [feq, hb0] at hab
  simp [hf0 h] at hab
  rcases hab with eq | zero
  · rwa [sub_eq_zero] at eq
  simp [zero, f0 h, hf0 h] at feq
  rwa [← zero] at feq

lemma hsq: ∀x, f (x* f x) = x^2 := by
  intro x
  have hx := h x 0
  simp [f0 h] at hx
  assumption

lemma f_odd: ∀x, - f x = f (-x) := by
  intro x
  by_cases! hx: x = 0
  · simp [hx, f0 h]
  have hsqa:= hsq h x
  have hsqb := hsq h (-x)
  rw [neg_sq, ← hsqa] at hsqb
  apply hinj h at hsqb
  rw [neg_mul, neg_eq_iff_eq_neg, ← mul_neg] at hsqb
  apply mul_left_cancel₀ hx at hsqb
  symm; assumption

lemma f2x: ∀x, f (2*x) = 2*f x := by
  intro x
  by_cases! hx: x = 0
  · simp [hx, f0 h]
  let y := x * sqrt 2 / 2
  have hyy := h y y
  have hxx := h x x
  rw [hsq h] at hyy hxx
  ring_nf at hyy hxx
  have hy2:= hsq h (y*sqrt 2)
  have hx2 := hsq h (x*sqrt 2)
  ring_nf at hy2 hx2
  norm_num at hy2 hx2
  ring_nf at hx2
  rw [← hyy] at hy2
  rw [← hxx] at hx2
  apply hinj h at hy2
  apply hinj h at hx2
  unfold y at hy2
  ring_nf at hy2
  field_simp at hy2
  norm_num at hy2
  rw [mul_comm x] at hy2
  rw [← hy2] at hx2
  ring_nf at hx2
  norm_num at hx2
  rw [mul_assoc, mul_left_comm] at hx2
  apply mul_left_cancel₀ hx at hx2
  symm
  rwa [mul_comm 2 x]


lemma f1: f 1 = 1 ∨ f 1 = -1 := by
  have hf1: ∀x, f x = 1 → (x = 1 ∨ x = -1) := by
    intro x fx1
    have hx1:= h x 0
    simp [f0 h, fx1] at hx1
    symm at hx1
    rwa [sq_eq_one_iff] at hx1
  have ff1: f (f 1) = 1 := by
    have h1 := hsq h 1
    simp at h1
    assumption
  specialize hf1 (f 1) ff1
  assumption





theorem idpos: f 1 = 1 → ∀x, f x = x:= by
  intro f1 y

  have f2:= f2x h 1
  simp [f1] at f2
  have fa1: ∀x, f (f (x+1)) = f x + 1 := by
    intro x
    have h1 := h 1 x
    simp [f1] at h1
    rwa [add_comm]
  have h1 := fa1 (y+1)
  ring_nf at h1
  have h2 := h 2 y
  simp [f2] at h2
  rw [mul_comm y 2] at h2
  simp [f2x h] at h2
  field_simp at h2
  rw [h1] at h2
  rw [show f y + 2 = 1 + (f y + 1) by ring_nf, add_left_cancel_iff, add_comm] at h2
  have h1a := fa1 y
  rw [← h2] at h1a
  apply hinj h at h1a
  rw [h2] at h1a
  simp at h1a
  assumption

theorem idneg: f 1 = -1 → ∀x, f x = -x := by
  intro f1 y
  have f2:= f2x h 1
  simp [f1] at f2
  have fa1: ∀x, f (f (x+1)) = f (-x) + 1 := by
    intro x
    have h1 := h 1 x
    simp [f1] at h1
    rwa [add_comm]
  have hf2: ∀y, f (-1 - y) = f (-y) + 1 := by
    intro y
    have h1 := fa1 (y+1)
    ring_nf at h1
    have h2 := h 2 y
    simp [f2] at h2
    rw [← neg_mul, mul_comm (-y), f2x h, f2x h] at h2
    field_simp at h2
    rwa [h1, add_comm, show (2:ℝ) = 1+1 by norm_num, ← add_assoc, add_right_cancel_iff] at h2
  have h2 := hf2 y
  rw [← neg_add', ← f_odd h, ← f_odd h, neg_add_eq_sub, neg_eq_iff_eq_neg, neg_sub, add_comm] at h2
  have h1 := fa1 y
  rw [h2, ← hf2] at h1
  apply hinj h at h1
  ring_nf at h1
  rwa [sub_eq_add_neg _ y, add_left_cancel_iff] at h1






snip end

omit f h in
problem IMO2009SLA7(f:ℝ→ℝ): f ∈ solution_set ↔ (∀x y, f (x*f (x+y)) = f (y* f x) + x^2):= by
  constructor
  intro h x y
  simp at h
  rcases h with pos | neg
  simp [pos]
  ring_nf
  simp [neg]
  ring_nf
  intro h
  have hf1 := f1 h
  rcases hf1 with pos | neg
  have idx := idpos h pos
  simp; left
  funext w
  exact idx w
  have idx := idneg h neg
  simp; right
  funext w
  exact idx w



end imo2009a7
