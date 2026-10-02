/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Order.Positive.Field
public import ProblemExtraction



@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMC 1999 p4
Find all strictly monotonic functions where f(x^2/f(x)) = x in ℝ+
-/

namespace imc1999p4
open  Function
abbrev PosReal : Type := { x : ℝ // 0 < x }
notation "ℝ+" => PosReal

example : MulArchimedean PosReal := inferInstance
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

@[simp]
theorem PosReal.coe_pow (a: ℝ+)(b: ℕ): (a^b).val = a.val ^ b := by rfl

@[simp]
theorem PosReal.coe_zpow (a: ℝ+)(b: ℤ): (a^b).val = a.val ^ b := by rfl


@[simp]
theorem PosReal.coe_inv (a: ℝ+): (a.val)⁻¹ = (a⁻¹).val := by rfl

determine solution_set: Set (ℝ+→ℝ+) := {f | ∃c, ∀x, f x = x*c}
problem imc1999q4(f:ℝ+→ℝ+)(hmono: StrictMono f): f ∈ solution_set ↔ ∀x, f (x^2 / f x) = x:= by
  constructor
  intro hf x
  obtain ⟨c, hc⟩ := hf
  simp [hc]
  rw [div_mul, mul_div_cancel_right, pow_two, mul_div_cancel_right]
  intro h
  unfold solution_set
  have hinj: Injective f := by exact StrictMono.injective hmono
  let g := fun y ↦ f y / y
  have hsurj: Surjective f := by
    intro x
    use (x^2 / f x)
    apply h

  have hfratio: ∀x, f x / x = f (f x)/(f x) := by
    intro x
    have h1 := h (f x)
    apply hinj at h1
    symm
    rwa [pow_two, mul_div_assoc, mul_comm, ← eq_div_iff_mul_eq', div_eq_div_iff_comm] at h1

  have hfg: ∀n,∀x, f x / x = f ^[n+1] x / f^[n] x := by
    intro n
    induction n with
    |zero => simp
    |succ n hn =>
      intro x
      rw [iterate_succ_apply f n, iterate_succ_apply, ← hn (f x)]
      apply hfratio

  have fiter: ∀x, ∀n, f^[n] x = x * (g x)^n := by
    intro x n
    induction n with
    |zero => simp
    |succ d hd =>
      rw [pow_succ, ← mul_assoc, ← hd, ← div_eq_iff_eq_mul']
      unfold g
      symm
      apply hfg d

  have ⟨f', hlf, hrf⟩:= bijective_iff_has_inverse.mp ⟨hinj, hsurj⟩
  unfold RightInverse at hrf
  have fiter_neg:  ∀n:ℕ,∀x,f'^[n] x = x * (g x)^(-↑(n:ℤ)) := by
    intro n
    induction n with
    |zero => simp
    |succ d hd =>
      intro x
      unfold g
      norm_cast
      rw [zpow_negSucc, pow_succ,mul_inv, ← mul_assoc, ← zpow_natCast,← zpow_neg, ←hd, iterate_succ_apply']
      simp
      rw [← div_eq_iff_eq_mul']
      have ⟨w, hw⟩: ∃w, f'^[d+1] x = w := by simp
      have hfw: f^[d+1] w = x := by
        rw [← hw, RightInverse.iterate hrf]
      have hwf: f'^[d] x = f w := by
        rw [← hfw, iterate_succ_apply, LeftInverse.iterate hlf]
      rw [← iterate_succ_apply' f', Nat.succ_eq_add_one, hw, hwf, ← hfw]
      rw [div_eq_div_iff_comm, ← iterate_succ_apply' f, Nat.succ_eq_add_one, show d+1+1 = d+2 by ring]
      apply hfg (d+1) w





  have gconst: ∀x y, g x = g y:= by
    intro x y
    by_cases! heq: x = y
    rw [heq]
    wlog! hxy: x < y generalizing x y
    apply lt_or_eq_of_le at hxy
    simp [heq.symm] at hxy
    exact (this y x heq.symm hxy).symm
    rw [forall_comm] at fiter
    have xgxmono: ∀n:ℤ, x * g x ^ n < y * g y ^ n := by
      intro n
      induction n with
      |zero => simp; lia
      |succ k hk =>
        norm_cast
        rw [← fiter, ← fiter]
        apply StrictMono.iterate hmono
        assumption
      |pred k hk =>
        rw [← neg_add', show -((k:ℤ) + 1) = -(↑(k + 1):ℤ) by rfl]
        rw [← fiter_neg ((k+1):ℕ),← fiter_neg ((k+1):ℕ)]
        have h1: f^[k+1] (f'^[k + 1] x) < f^[k+1] (f'^[k + 1] y):= by
          rwa [LeftInverse.iterate hrf, LeftInverse.iterate hrf]
        rwa [StrictMono.lt_iff_lt (StrictMono.iterate hmono (k+1))] at h1


    have xgx_one: ∀n:ℤ, 1 < y/x * (g y /g x)^ n := by
      intro n
      have h1 := xgxmono n
      rwa [← one_lt_div', mul_comm x, div_mul_eq_div_mul_one_div, mul_div_assoc, ← div_zpow, ← mul_rotate, one_div_mul_eq_div] at h1


    rcases (lt_trichotomy (g y) (g x)) with lt | eq | gt
    have ⟨r, hr⟩: ∃r, r = g y / g x := by simp
    have ⟨c, c1, hc⟩: ∃c, c > 1 ∧  c = y/x := by simp; lia
    rw [←hr, ← hc] at xgx_one
    have h1c: (0:ℝ) < (1:ℝ+)/c := by
      rw [div_pos_iff_of_pos_left]
      lia; norm_num

    have r1: r < 1:= by
      rw [hr]
      simp
      assumption

    have ⟨n', hn'⟩:= exists_pow_lt_of_lt_one h1c r1
    norm_cast at hn'
    rw [← PosReal.coe_pow, ← PosReal.coe_div] at hn'
    norm_cast at hn'
    specialize xgx_one n'
    rw [mul_comm, ← div_lt_iff_lt_mul] at xgx_one
    apply le_of_lt at hn'
    absurd hn'
    push Not
    assumption
    symm
    assumption
    have ⟨c, c1, hc⟩: ∃c, c > 1 ∧  c = y/x := by simp; lia
    rw [← hc] at xgx_one
    have xgx': ∀ (n : ℤ), (g x / g y)^n < c := by
      intro n
      specialize xgx_one n
      rwa [div_zpow, mul_comm, ← div_lt_iff_lt_mul', one_div_div, ← div_zpow] at xgx_one

    have i1: (1:ℝ) < ((g y / g x):ℝ) := by
      rw [one_lt_div]
      exact_mod_cast gt
      grind
    have h1c: (0:ℝ) < (1:ℝ+)/c := by
      rw [div_pos_iff_of_pos_left]
      lia; norm_num
    suffices hm: ∃m:ℤ, c < (g y / g x)^m
    obtain ⟨m, hm⟩ := hm
    specialize xgx' (-m)
    rw [zpow_neg, inv_eq_one_div, div_zpow] at xgx'
    norm_cast at xgx'
    rw [one_div_div, ← div_zpow] at xgx'
    absurd hm
    push Not
    exact le_of_lt xgx'
    use ⌈Real.logb ((g y / g x):ℝ) (c+1)⌉
    apply Subtype.coe_lt_coe.mp
    have e1: c = ((g y / g x):ℝ)^(Real.logb ((g y / g x)) c) := by
      rw [Real.rpow_logb]
      rw [← PosReal.coe_div]; grind
      linarith; lia
    nth_rw 1 [e1]
    rw [← PosReal.coe_div, PosReal.coe_zpow, ← Real.rpow_intCast, Real.rpow_lt_rpow_left_iff]
    have i3: Real.logb (↑(g y / g x)) (↑c + 1) ≤ ↑⌈Real.logb (↑(g y / g x)) (↑c + 1)⌉ := by apply Int.le_ceil
    suffices: Real.logb (↑(g y / g x)) c < Real.logb (↑(g y / g x)) (↑c + 1)
    linarith
    rw [Real.logb_lt_logb_iff]; linarith
    simp; assumption
    grind; grind; simp; assumption



  unfold g at gconst
  have ⟨c, hgc⟩: ∃c, ∀x, f x = x*c := by
    use f 1
    intro x
    have h1 := gconst x 1
    simp at h1
    rwa [div_eq_iff_eq_mul'] at h1

  use c

end imc1999p4
