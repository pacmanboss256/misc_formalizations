/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Interval.Set.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 2005 A2
Find all functions f: ℝ+ → ℝ+ such that
f(x) * f(y) = 2 * f(x + y * f(x)) in ℝ+
-/

namespace imo2005A2


determine solution_set: Set (ℝ→ℝ):= {fun _ ↦ 2}
open Set
snip begin
variable {f:ℝ→ℝ}(fpos: ∀i, 0 < f i)(h:∀x y, x > 0 → y > 0 → f x * f y = 2 * f (x+ y*f x))
include f fpos h

lemma hxyz: ∀x y z, x > 0 → y > 0 → z>0 → f (x + z*f x + (y*f x * f z)/2) = f (x + z*f x + (y*f x * f z)) := by
  intro x y z hx hy hz
  have fpos':= fpos
  have hxz: f (x+ z*f x) = (f x * f z) / 2 := by
    have h0 := h x z hx hz
    field_simp
    symm
    rwa [mul_comm _ 2]

  have i1: x + z * f x > 0 := by
    apply add_pos hx
    apply mul_pos hz
    apply fpos
  have h1 := h (x + z*f x) y i1 hy
  rw [hxz] at h1
  apply_fun (2 * · ) at h1
  nth_rw 2 [← mul_assoc] at h1
  rw [← mul_assoc, ←mul_div_assoc, mul_div_right_comm, div_self] at h1
  simp at h1
  have i2: z + y * f z > 0 := by
    apply add_pos hz
    apply mul_pos hy
    apply fpos
  have h2:= h x (z+y*f z) hx i2
  have hyz: f (z+ y*f z) = (f z * f y) / 2 := by
    have h0 := h z y hz hy
    field_simp; symm
    rwa [mul_comm _ 2]
  rw [hyz] at h2
  apply_fun (2 * · ) at h2
  nth_rw 2 [← mul_assoc] at h2
  rw [← mul_assoc, ←mul_div_assoc, mul_div_right_comm, mul_div_right_comm, div_self] at h2
  simp at h2
  rw [← mul_assoc, h1] at h2
  simp at h2
  rwa [← mul_div_assoc, ← mul_assoc, add_mul, ← add_assoc, mul_right_comm y (f z)] at h2
  all_goals positivity


lemma hconst: ∀a b, 0 < a → a < b → b < 2 * a → f a = f b:= by
  intro a b ha hab h2ab
  have ⟨x, xpos, hx⟩: ∃x, x > 0 ∧ x = a - b/2 := by
    simp
    field_simp
    assumption
  have ⟨z, zpos, hz⟩: ∃z, z > 0 ∧ z = (2*a-b-x)/(f x) := by
    simp
    rw [div_pos_iff_of_pos_right (by apply fpos)]
    linarith
  have ⟨y, ypos, hy⟩: ∃y, y > 0 ∧ y = 2*(b-a)/(f x * f z) := by
    simp
    rw [div_pos_iff_of_pos_right]
    linarith
    apply mul_pos <;> apply fpos
  have i2a:= fpos x
  have i2b := fpos z
  have hxyzab := hxyz fpos h x y z xpos ypos zpos
  nth_rw 1 4 [hx] at hxyzab
  nth_rw 1 3 [hz] at hxyzab
  rw [div_mul_comm, div_self, hy] at hxyzab
  simp [div_mul_comm] at hxyzab
  field_simp at hxyzab
  rw [hx] at hxyzab
  ring_nf at hxyzab
  assumption
  all_goals positivity

lemma hconst_in: ∀a, 0 < a → ∃c, ∀w ∈ Set.Ioo a (2*a), f w = c := by
  intro a apos
  use (f a)
  simp
  intro x ax x2a
  exact (hconst fpos h a x apos ax x2a).symm

lemma hconst_domain: ∀x > 0, ∃ c, f x = c := by

  intro x xpos

  have hcover: ∃c, ∀k:ℤ, ∀x ∈ Set.Ioo ((3/2)^k) (2*(3/2)^k), f x = c := by
    have ⟨c, hc⟩:= hconst_in fpos h 1 (by positivity)
    simp at hc
    use c
    intro k
    induction k with
    |zero =>
      simp
      intro x hx hx2
      exact hc x hx hx2
    |succ k hk =>
      have ⟨c1, hc1⟩:= hconst_in fpos h ((3/2)^(k+1)) (by positivity)
      have inter: (((3:ℝ)/2)^(k+1)) < 2*((3/2)^k) := by
        rw [pow_succ',mul_lt_mul_iff_of_pos_right (by positivity)]
        linarith
      suffices: ∃y, y ∈ (Set.Ioo (((3:ℝ) / 2) ^ (k + 1)) (2 * (3 / 2) ^ (k + 1)) ∩ Set.Ioo (((3:ℝ) / 2) ^ k) (2 * (3 / 2) ^ k))
      obtain ⟨y, hy1, hy2⟩:= this
      have hfy:= hc1 y hy1
      have hfy2:= hk y hy2
      rw [hfy2] at hfy
      rw [hfy]
      apply hc1
      have ⟨y', hy'⟩:= exists_between inter
      use y'
      simp
      constructor
      constructor
      lia
      trans (2:ℝ)*(3/2)^k
      lia; simp [pow_lt_pow_right₀ (by linarith: 1 < (3:ℝ)/2)]
      constructor
      trans ((3:ℝ)/2)^(k+1)
      simp [pow_lt_pow_right₀ (by linarith: 1 < (3:ℝ)/2)]
      lia; lia
    |pred k hk =>
      have ⟨c1, hc1⟩:= hconst_in fpos h ((3/2)^(-(k:ℤ)-1)) (by positivity)
      have inter: (((3:ℝ)/2)^(-(k:ℤ))) < 2*((3/2)^(-(k:ℤ)-1)) := by
        rw [neg_sub_left, zpow_neg, add_comm, zpow_neg]
        norm_cast
        rw [pow_succ, mul_comm 2, mul_inv]
        norm_cast
        field_simp
        linarith
      suffices: ∃y, y ∈ (Set.Ioo (((3:ℝ) / 2) ^ (-(k:ℤ)-1))) (2 * (3 / 2) ^ (-(k:ℤ)-1)) ∩ Set.Ioo (((3:ℝ) / 2) ^ (-(k:ℤ))) (2 * (3 / 2) ^ (-(k:ℤ)))
      obtain ⟨y, hy1, hy2⟩:= this
      have hfy:= hc1 y hy1
      have hfy2:= hk y hy2
      rw [hfy2] at hfy
      rw [hfy]
      apply hc1
      have ⟨y', hy'1, hy'2⟩:= exists_between inter
      use y'
      simp
      constructor
      constructor
      trans (3 / 2) ^ (-k:ℤ)
      apply zpow_lt_zpow_right₀ (by linarith: 1 < (3:ℝ)/2); simp
      assumption; assumption
      constructor
      simp at hy'1; assumption
      trans 2*((3:ℝ)/2)^(-(k:ℤ)-1)
      assumption
      rw [neg_sub_left, zpow_neg, add_comm]
      norm_cast
      rw [pow_succ, mul_inv, ← mul_assoc]
      field_simp; linarith

  have ⟨c, hc⟩ := hcover



























snip end

problem imo2005SLA2(f:ℝ+→ℝ+): f ∈ solution_set ↔ ∀x y, f x * f y = 2 * f (x+ y*f x) := by
  constructor
  · intro hf x y
    simp at hf
    simp [hf]
  intro h


  sorry

end imo2005A2
