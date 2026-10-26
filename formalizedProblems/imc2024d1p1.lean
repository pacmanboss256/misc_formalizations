/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMC 2024 day 1 problem 1
Determine all pairs (a,b) ∈ ℂ² where |a|=|b|=1 and a+b+a b* ∈ ℝ
-/
namespace imc2024
open Complex Real
determine solution_set: Set (ℂ × ℂ):= {(a,b)| (a = 1 ∧ ‖b‖ = 1) ∨(‖a‖ = 1 ∧ b = -1) ∨ (‖a‖ = 1 ∧ ‖b‖ = 1 ∧ b = -a)}

problem imc2024d1p1: ∀a b, (((a,b) ∈ solution_set ↔ (‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a+b+a* star b).im = 0))):= by
  intro a b
  constructor
  intro abs
  unfold solution_set at abs
  simp at abs
  rcases abs with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  <;> simp [ha, hb]
  ring_nf
  intro ⟨ha, hb, hr⟩
  have hr' := hr
  rw [norm_eq_one_iff'] at ha hb
  simp at ha hb
  obtain ⟨x, ⟨hx1, hx2⟩, ha⟩ := ha
  obtain ⟨y, ⟨hy1, hy2⟩, hb⟩ := hb
  rw [← hb, ← ha] at hr
  simp at hr
  rw [neg_add_eq_sub, ← Real.sin_sub, show (x-y) = (2*((x-y)/2)) by ring,Real.sin_add_sin] at hr
  rw [Real.sin_two_mul, mul_assoc, mul_assoc, ← mul_add, ← add_mul, Real.sin_add_sin] at hr
  ring_nf at hr
  rw [mul_eq_zero_iff_right (by positivity),mul_eq_zero, mul_eq_zero] at hr
  rcases hr with ⟨h1 | h2⟩ | h3
  rw [Real.sin_eq_zero_iff] at h1
  obtain ⟨n, hn⟩ := h1
  field_simp at hn
  rw [← hn] at ha
  simp at ha
  rw [mul_assoc, mul_assoc, ← mul_left_comm 2, ← mul_assoc 2] at ha
  simp at ha
  simp; left; simp [ha]
  rw [norm_eq_one_iff]
  use y
  rw [Real.cos_eq_zero_iff] at h2
  obtain ⟨n, hn⟩ := h2
  field_simp at hn
  rw [hn] at hb
  simp at hb
  ring_nf at hb
  simp at hb
  rw [show ↑n * ↑π * I * 2 = ↑n * (2 * ↑π * I) by ring] at hb
  simp at hb
  simp; right; left; simp [hb]
  rw [norm_eq_one_iff]; use x
  rw [show x * (1 / 2) + y * (-1 / 2) = x/2 - y/2 by ring, Real.cos_eq_zero_iff] at h3
  obtain ⟨k, hk⟩ := h3
  field_simp at hk
  rw [sub_eq_iff_eq_add'] at hk
  have k0: k=0 ∨ k = -1 := by
    rw [hk] at hx1 hx2
    ring_nf at hx1 hx2
    have i1: -3*π < π * ↑k * 2:= by linarith
    have i2: π * ↑k * 2 ≤ π := by linarith
    field_simp at i1 i2
    ring_nf at i1
    norm_cast at i2
    have i3: k ≤ 0 := by grind
    clear i2
    norm_cast at i1
    simp at i1
    have i4: -1 ≤ k := by grind
    grind

  rcases k0 with zero | one
  simp [zero] at hk
  rw [hk] at ha
  push_cast at ha
  rw [add_mul] at ha
  simp at ha
  simp; right; right
  simp [← ha,← hb]
  rw [one] at hk
  norm_num at hk
  rw [← sub_eq_add_neg] at hk
  rw [hk] at ha
  push_cast at ha
  rw [sub_mul] at ha
  simp at ha
  simp; right; right
  simp [← ha,← hb]












end imc2024
