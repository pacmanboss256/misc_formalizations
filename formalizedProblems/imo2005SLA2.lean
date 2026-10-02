/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Interval.Set.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 2005 A2
Find all functions f: ℝ≥0+ → ℝ≥0+ such that
f(x) * f(y) = 2 * f(x + y * f(x)) in ℝ≥0+
-/

namespace imo2005A2
open Set NNReal
determine solution_set: Set (ℝ≥0→ℝ≥0):= {fun _ ↦ 2}


snip begin
variable {f:ℝ≥0→ℝ≥0}(fpos: ∀i, 0 < f i)(h:∀x y, x > 0 → y > 0 → f x * f y = 2 * f (x+ y*f x))
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
  have i0: 0 < 2 * (b - a) := by
    apply mul_pos
    positivity
    simp; assumption
  have i0':  a - b / 2 < 2 * a - b := by
    rify
    rw [NNReal.coe_sub_of_lt (by linarith),NNReal.coe_sub_of_lt (by linarith)]
    norm_num
    linarith
  have ⟨x, xpos, hx⟩: ∃x, x > 0 ∧ x = a - b/2 := by
    simp
    field_simp
    assumption
  have ⟨z, zpos, hz⟩: ∃z, z > 0 ∧ z = (2*a-b-x)/(f x) := by
    simp
    rw [div_pos_iff_of_pos_right (by apply fpos), hx]
    simp
    assumption
  have ⟨y, ypos, hy⟩: ∃y, y > 0 ∧ y = 2*(b-a)/(f x * f z) := by
    simp
    rw [div_pos_iff_of_pos_right]
    lia
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
  have e1: a - b / 2 + (2 * a - b - (a - b / 2)) + (b - a) = a := by
    rify
    rw [NNReal.coe_sub_of_lt (by linarith), NNReal.coe_sub_of_lt (by linarith), NNReal.coe_sub_of_lt (by linarith)]
    rw [NNReal.coe_sub_of_lt (by linarith),  NNReal.coe_sub_of_lt (by linarith)]
    norm_num
    ring_nf
  have e2: a - b / 2 + (2 * a - b - (a - b / 2)) + 2 * (b - a) = b := by
    rify
    rw [NNReal.coe_sub_of_lt (by linarith), NNReal.coe_sub_of_lt (by linarith), NNReal.coe_sub_of_lt (by linarith)]
    rw [NNReal.coe_sub_of_lt (by linarith),  NNReal.coe_sub_of_lt (by linarith)]
    norm_num
    ring_nf
  rwa [e1, e2] at hxyzab
  all_goals positivity

lemma hconst_in: ∀a, 0 < a → ∃c, ∀w ∈ Set.Ioo a (2*a), f w = c := by
  intro a apos
  use (f a)
  simp
  intro x ax x2a
  exact (hconst fpos h a x apos ax x2a).symm

lemma hconst_domain: ∃ c, ∀x > 0, f x = c := by
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
      have inter: (((3:ℝ≥0)/2)^(k+1)) < 2*((3/2)^k) := by
        rw [pow_succ',mul_lt_mul_iff_of_pos_right (by positivity)]
        linarith
      suffices: ∃y, y ∈ (Set.Ioo (((3:ℝ≥0) / 2) ^ (k + 1)) (2 * (3 / 2) ^ (k + 1)) ∩ Set.Ioo (((3:ℝ≥0) / 2) ^ k) (2 * (3 / 2) ^ k))
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
      trans (2:ℝ≥0)*(3/2)^k
      lia; simp [pow_lt_pow_right₀ (by linarith: 1 < (3:ℝ≥0)/2)]
      constructor
      trans ((3:ℝ≥0)/2)^(k+1)
      simp [pow_lt_pow_right₀ (by linarith: 1 < (3:ℝ≥0)/2)]
      lia; lia
    |pred k hk =>
      have ⟨c1, hc1⟩:= hconst_in fpos h ((3/2)^(-(k:ℤ)-1)) (by positivity)
      have inter: (((3:ℝ≥0)/2)^(-(k:ℤ))) < 2*((3/2)^(-(k:ℤ)-1)) := by
        rw [neg_sub_left, zpow_neg, add_comm, zpow_neg]
        norm_cast
        rw [pow_succ, mul_comm 2, mul_inv]
        norm_cast
        field_simp
        linarith
      suffices: ∃y, y ∈ (Set.Ioo (((3:ℝ≥0) / 2) ^ (-(k:ℤ)-1))) (2 * (3 / 2) ^ (-(k:ℤ)-1)) ∩ Set.Ioo (((3:ℝ≥0) / 2) ^ (-(k:ℤ))) (2 * (3 / 2) ^ (-(k:ℤ)))
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
      apply zpow_lt_zpow_right₀ (by linarith: 1 < (3:ℝ≥0)/2); simp
      assumption; assumption
      constructor
      simp at hy'1; assumption
      trans 2*((3:ℝ≥0)/2)^(-(k:ℤ)-1)
      assumption
      rw [neg_sub_left, zpow_neg, add_comm]
      norm_cast
      rw [pow_succ, mul_inv, ← mul_assoc]
      field_simp; linarith

  have ⟨c, hc⟩ := hcover
  rw [← Set.forall_mem_iUnion] at hc

  have cov_eq_univ: {j:ℝ≥0|0 < j} = ⋃ (i:ℤ), Ioo ((3 / 2) ^ i) (2 * (3 / 2) ^ i) := by
    ext y
    constructor
    simp
    intro hy
    have ⟨n, hn1, hn2⟩:= exists_mem_Ioc_zpow hy (by linarith: (1:ℝ≥0)<3/2)
    use n
    constructor
    assumption
    apply LE.le.trans_lt hn2
    rw [← rpow_intCast]
    push_cast
    rw [rpow_add_one]
    norm_cast
    rw [mul_comm]
    field_simp
    linarith; linarith
    simp
    intro i hi hy2
    linarith
  rw [← cov_eq_univ] at hc
  simp at hc
  use c


lemma f_const: ∀x, 0 < x → f x = 2:= by
  intro x xpos
  have hx := h x x xpos xpos
  have ⟨c, hc⟩ := hconst_domain fpos h
  have cpos: 0 < c := by
    rw [← hc x xpos]
    apply fpos
  rw [hc x xpos, hc (x+x*c) (by positivity)] at hx
  field_simp at hx
  specialize hc x xpos
  rwa [hx] at hc





snip end

omit f fpos h in
problem imo2005SLA2(f:ℝ≥0→ℝ≥0)(fpos: ∀i, 0 < f i)(f0: f 0 = 2): f ∈ solution_set ↔ ∀x y, x > 0 → y > 0 → f x * f y = 2 * f (x+ y*f x) := by
  constructor
  · intro hf x y hx hy
    simp at hf
    simp [hf]
  intro h
  have h1 := f_const fpos h
  simp
  funext w
  by_cases! hw: w ≤ 0
  simp at hw
  rwa [hw]
  exact h1 w hw
end imo2005A2
