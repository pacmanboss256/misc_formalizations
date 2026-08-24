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
## IMO Shortlist 2002 A1
Find all functions f : ℝ → ℝ such that
f(f(x) + y)=2x + f(f(y)-x) for all x,y ∈ ℝ
-/

namespace imo2002A1
open Real Function

determine solution_set: Set (ℝ→ℝ) := {f | ∃c, ∀ x, f x = x + c}

theorem imo2002SLA1(f:ℝ→ℝ): f ∈ solution_set ↔  ∀x y, f (f x + y) = 2*x + f (f y - x) := by
  constructor
  · simp
    intro c h x y
    simp [h]
    ring_nf
  intro h
  let a := f 0

  have hsurj : ∀(x:ℝ), ∃z, f z = a - 2*x  := by
    intro x
    specialize h x (-f x)
    simp at h
    generalize f (-f x) - x = z at h
    apply sub_eq_of_eq_add' at h
    symm at h
    use z

  have hr := hsurj (a/2)
  ring_nf at hr
  obtain ⟨r,hr⟩ := hr

  have fa : f (-a) = 0 := by
    have hw := h r
    simp [hr] at hw
    choose y hy using hsurj ((a-r)/2)
    specialize hw y
    ring_nf at hy
    rw [hy] at hw
    ring_nf at hw
    rw [mul_two] at hw
    nth_rw 1 [← add_zero r] at hw
    rw [add_assoc, add_left_cancel_iff] at hw
    symm at hw
    rw [add_eq_zero_iff_eq_neg] at hw
    change r = -a at hw
    rwa [← hw]
  have z': ∀z, f (a + z) = f (f z) := by
    intro z
    have hz := h 0 z
    simp at hz
    change f (a + z) = f (f z) at hz
    assumption
  have y': ∀z, f (z + a) = 2 * a + z := by
    intro z
    choose y hy using hsurj ((a - z)/2)
    have ha := h (-a) y
    simp [fa] at ha
    symm at ha
    rw [neg_add_eq_iff_eq_add] at ha
    ring_nf at hy
    rwa [hy] at ha
  have hz : ∀y, f (f y) = 2 * a + y := by
    intro y
    specialize z' y
    specialize y' y
    rw [add_comm] at y'
    exact Eq.trans z'.symm y'

  have hinj : Injective f := by
    intro x y hf
    have hx := hz x
    have hy := hz y
    nth_rw 1 [hf] at hx
    have heq := Eq.trans hx.symm hy
    simp at heq
    assumption

  use a
  intro x
  specialize z' x
  apply hinj
  symm
  rw [add_comm]
  assumption



end imo2002A1
