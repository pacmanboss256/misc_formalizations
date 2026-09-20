/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Algebra.Order.Positive.Field
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 2016 A4
Find all functions f: ℝ+ → ℝ+ such that
x * f(x^2) * f(f(y)) + f(y * f(x)) = f(x * y) * (f(f(x^2)) + f(f(y^2))) for all x,y in ℝ+
-/

namespace imo2016A4
open  Function
abbrev PosReal : Type := { x : ℝ // 0 < x }
notation "ℝ+" => PosReal

lemma PosReal.lt_add (a b : ℝ+) : a < a + b := by
  obtain ⟨b, bpos⟩ := b
  apply Subtype.mk_lt_mk.mpr
  linarith

@[simp]
theorem PosReal.coe_mul (a b : ℝ+) : (a * b).val = a.val * b.val := rfl

@[simp]
theorem PosReal.coe_add (a b : ℝ+) : (a + b).val = a.val + b.val := rfl

@[simp]
theorem PosReal.coe_div (a b : ℝ+) : (a / b).val = a.val / b.val := rfl


def condition(f:ℝ+ → ℝ+):= ∀x y, x * f (x^2) * f (f y) + f (y * f x) =
  f (x * y) * (f (f (x^2)) + f (f (y^2)))

snip begin

variable {f: ℝ+ → ℝ+}(hf: condition f)
include f hf


lemma f1: f 1 = 1 := by
  have h1 := hf 1 1
  simp at h1
  let c := f 1
  change c * f c + f c = c * (f c + f c) at h1
  rw [mul_add] at h1
  rwa [add_left_cancel_iff, right_eq_mul] at h1

lemma l1: ∀x, f (f x) = (f x) * (f (f (x^2))) := by
  intro x
  have h1 := hf 1 x
  simp [f1 hf] at h1
  rw [mul_add, add_comm] at h1
  simp at h1
  assumption

lemma l2: ∀x, x * f (x^2) = f x := by
  intro x
  have h1 := hf x 1
  simp [f1 hf] at h1
  rw [mul_add] at h1
  rwa [← l1 hf x, add_comm, mul_one, add_left_cancel_iff] at h1

lemma l3: ∀x, f x * f (1/x) = 1 := by
  intro x
  have h1:= hf x (1/x)
  rw [l2 hf x] at h1
  nth_rw 2 [← l2 hf x] at h1
  rw [← mul_assoc, mul_comm (1/x), mul_div_left_comm, div_self'] at h1
  simp at h1
  rw [f1 hf, one_mul, add_comm, add_left_cancel_iff] at h1
  rw [inv_eq_one_div, inv_eq_one_div, l1 hf (1/x), ← mul_assoc, show (1/x)^2 = 1/x^2 by simp] at h1
  rwa [mul_eq_right] at h1

lemma l4: ∀x,f (f x)/ f x =  f (f (x^2)) := by
  intro x
  rw [l1 hf x, mul_comm, mul_div_assoc, div_self']
  simp



lemma finj: ∀x y, f x = f y → x = y := by
  intro a b feq
  by_contra! abeq
  have fmul: ∀y, f (a*y) = f (b*y) := by
    intro y
    have ha := hf a y
    have hb := hf b y
    rw [l2 hf a, feq] at ha
    rw [l2 hf b, ha] at hb
    clear ha
    rw [← l4 hf a, ← l4 hf b, feq] at hb
    rwa [mul_right_cancel_iff] at hb
  have ⟨t, ht⟩: ∃t, t = b/a := by
    use b/a
  specialize fmul (1/a)
  rw [mul_one_div, div_self', mul_one_div, ← ht] at fmul
  have ft := fmul.symm
  simp [f1 hf] at ft
  have ht2: f (t^2) = 1/t := by
    symm at fmul
    rwa [← l2 hf t, f1 hf, mul_comm, ← eq_div_iff_mul_eq'] at fmul
  have ht1: f (1/t) = 1 := by
    rw [f1 hf, ← l3 hf t, ft, one_mul] at fmul
    assumption
  have htt := hf t t
  rw [← pow_two] at htt
  simp only [ft, ht2, f1 hf, mul_one_div, div_self', one_mul, mul_one] at htt
  rw [ht1] at htt
  simp at htt
  symm at ht
  rw [htt, div_eq_one] at ht
  tauto

theorem sol: ∀x, f x = 1/x := by
  intro x
  have h1 := l4 hf x
  rw [← l2 hf, mul_comm, mul_div_assoc, div_self'] at h1
  simp at h1
  have h2: f (x^2) = f x / x := by
    have i1 := l2 hf x
    rwa [eq_div_iff_mul_eq'']
  rw [h2] at h1
  apply finj hf (f x ^2) (f x / x) at h1
  rwa [pow_two, div_eq_mul_one_div, mul_left_cancel_iff] at h1









snip end

determine solution_set: Set (ℝ+ → ℝ+) := {fun w ↦ 1 / w}

omit f hf in
problem imo2016SLA4(f:ℝ+ → ℝ+): f ∈ solution_set ↔ condition f := by
  constructor
  intro h x y
  unfold solution_set at h
  rw [Set.mem_singleton_iff] at h
  rw [h]
  ring_nf
  simp
  repeat rw [inv_eq_one_div]
  rw [pow_two, mul_div_assoc', mul_comm x 1]
  simp
  repeat rw [inv_eq_one_div]
  rw [one_div_mul_eq_div, mul_add, mul_one_div, mul_assoc, one_div_mul_eq_div x, mul_div_assoc, div_self', one_div_mul_eq_div, mul_one]
  rw [mul_right_comm, one_div_mul_eq_div, pow_two, mul_div_assoc, div_self', mul_one, mul_one_div]
  rw [add_comm]

  intro h
  unfold condition at h
  have s:= sol h
  unfold solution_set
  rw [Set.mem_singleton_iff]
  funext w
  exact s w



end imo2016A4
