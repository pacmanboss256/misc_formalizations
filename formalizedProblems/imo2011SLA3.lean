/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Real.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 2011 A3
Find all functions f, g: ℝ → ℝ such that
g(f(x+y)) = f x + (2x+y)*g(y) for all x,y in ℝ
-/

namespace imo2011A3
open Real

determine solution_set: Set ((ℝ→ℝ) × (ℝ→ℝ)):=
  {(f,g)|(∀x, f x = 0 ∧ g x = 0) ∨ (∃c, ∀x, f x = x^2 + c ∧ g x = x)}

snip begin
variable {f:ℝ→ℝ}{g:ℝ→ℝ}(h:∀x y, g (f (x+y)) = f x + (2*x+y)*(g y))
include f g h

lemma hq: ∀x y, f x - f y = (2*y+x)*(g x) - (2*x+y)*(g y):= by
  intro x y
  have h1:= h x y
  rw [add_comm, h y x, ← sub_eq_sub_iff_add_eq_add, sub_eq_sub_iff_sub_eq_sub, sub_eq_sub_iff_comm] at h1
  assumption

lemma hgx: ∀x, g x = (g 1 - g 0)*x + g 0 := by
  intro x
  have hq := hq h
  have h0 := hq 1 0
  ring_nf at h0
  have h1 := hq x 0
  have h2 := hq x 1
  ring_nf at h1 h2
  have h3: f x - f 0 - (f x - f 1) = x * g x - x * g 0 * 2 - (x * g x - x * g 1 * 2 + g x * 2 - g 1) := by
    rw [h1, h2]
  simp at h3
  rw [h0] at h3
  ring_nf at h3
  rw [sub_eq_add_neg, add_sub_assoc, add_sub_assoc, add_left_cancel_iff] at h3
  field_simp at h3
  rwa [eq_sub_iff_add_eq,add_comm, add_neg_eq_iff_eq_add, mul_comm] at h3

lemma zero_case: g 1 - g 0 = 0 → ∀x:ℝ, (f x = 0 ∧ g x = 0) := by
  intro hgz
  have ⟨c, hc⟩: ∃c, ∀x, g x = c := by
    use g 0
    have hgx' := hgx h
    rw [hgz] at hgx'
    simp at hgx'
    assumption
  have hfx: ∀x y, f x = c - 2*c*x - c * y := by
    intro x y
    have pg:= h x y
    simp [hc] at pg
    ring_nf at pg
    rw [add_assoc, ← sub_eq_iff_eq_add] at pg
    ring_nf at pg
    rw [← mul_rotate] at pg
    symm
    assumption

  intro x
  have hfx0 := hfx 0
  have h1 := hfx0 x
  have h2 := hfx0 (x+1)
  rw [h1] at h2
  clear h1
  simp at h2
  rw [h2] at hc
  symm
  constructor
  · exact hc x
  have h0 := h x 0
  simp [hc] at h0
  symm
  assumption





lemma non_zero: g 1 - g 0 ≠ 0 → (∀x:ℝ, f x = 0 ∧ g x = 0) ∨ ((∃c, ∀x, f x = x^2 + c ∧ g x = x)
) := by
  intro hgs
  have ⟨a, b, ⟨anz, hglin⟩⟩: ∃a b:ℝ, a≠0 ∧ ∀x, g x = a*x + b := by
    use g 1 - g 0, g 0
    simp [hgs]
    intro x
    exact hgx h x
  have ⟨c, hc⟩: ∃c, c = a*f 0 + b := by use a*f 0 + b
  have hfs: ∀x, f x = a * x ^ 2 - b * x + c := by
    intro x
    have h1 := h x (-x)
    ring_nf at h1
    rw [hglin] at h1
    ring_nf at h1
    rw [hglin, ← sub_eq_iff_eq_add'] at h1
    symm at h1
    rw [← hc] at h1
    ring_nf at h1
    rwa [sub_add_comm, mul_comm, mul_comm x b] at h1

  have hr: ∀x, a^2*x^2 - a*b*x + (a*c + b) = a*x^2 + b*x + c := by
    intro x
    have p1 := h 0 x
    simp [hglin, hfs] at p1
    ring_nf at p1
    rw [show -(a * x * b) + a * c + a ^ 2 * x ^ 2 + b = a ^ 2 * x ^ 2 - a * b * x + (a * c + b) by ring, mul_comm x b] at p1
    assumption
  have r0 := hr 0
  simp at r0
  simp [r0] at hr

  have r11 : b*(a+1) = 0 := by
    have r1 := hr (1)
    have r2 := hr (-1)
    simp at r1 r2
    have r3: a ^ 2 - a * b - (a ^ 2 + a * b) = a + b- (a + -b) := by
      rw [← r1, ←r2]
    ring_nf at r3
    field_simp at r3
    rw [neg_eq_iff_add_eq_zero, add_comm, mul_comm] at r3
    ring_nf
    assumption

  rw [mul_eq_zero] at r11
  rcases r11 with bz | an1
  by_cases! hcz: c = 0
  simp [hcz, bz] at hfs
  simp [bz] at r0
  rw [bz] at hglin
  right
  use 0
  intro x
  rw [hcz, bz] at hc
  simp [anz] at hc
  simp [hfs]
  simp at hglin
  have f0 := hfs 0
  have g0 := hglin 0
  ring_nf at f0 g0
  have hfg := (forall_comm.mp h) 0
  rename_bvar a → x at hfg
  simp [hfs, hglin, anz] at hfg
  constructor
  exact hfg x
  simp [bz] at hr
  by_cases! hx: x = 0
  simp [hglin x]
  rw [hx]
  simp
  specialize hr x
  simp [hx] at hr
  apply eq_zero_or_one_of_sq_eq_self at hr
  simp [anz] at hr
  simp [hr] at hglin
  exact hglin x
  right
  use c
  intro x
  simp [bz] at r0 hfs hglin hc
  rw [mul_left_eq_self₀] at r0
  simp [hcz] at r0
  constructor
  specialize hfs x
  rw [r0] at hfs
  rw [hfs]
  simp
  simp [hglin, r0]

  -- a+1 = 0

  rw [add_eq_zero_iff_eq_neg] at an1
  simp [an1] at hfs
  have hb: b = (2*c) := by
    simp [an1] at r0
    rwa [neg_add_eq_iff_eq_add, ← two_mul] at r0

  have h' := h 1 1
  simp [hfs, hglin, an1, hb] at h'
  ring_nf at h'
  rw [add_right_cancel_iff] at h'
  linarith
















snip end
omit f g h in
theorem imo2011SLA3(f:ℝ→ℝ)(g:ℝ→ℝ): (f,g) ∈ solution_set ↔ (∀x y, g (f (x+y)) = f x + (2*x+y)*(g y)) := by
  constructor
  intro h
  unfold solution_set at h
  rcases h with zero | sqid
  simp [zero]
  obtain ⟨c, hfg⟩:= sqid
  intro x y
  simp [hfg]
  ring_nf

  intro h
  by_cases! hgsub: g 1 - g 0 = 0
  have h1 := zero_case h hgsub
  simp; left
  assumption
  simp
  have h1:= non_zero h hgsub
  assumption



end imo2011A3
