/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 2010 SLA5
Find all functions f: ℚ+ → ℚ+ such that f(f(x)^2 * y) = x^3 * f(x*y)
-/

namespace imo2010a5
open Function Real

abbrev PRat := { q : ℚ // 0 < q }
notation "ℚ+" => PRat

lemma PRat.lt_add (a b : ℚ+) : a < a + b := by
  obtain ⟨b, bpos⟩ := b
  apply Subtype.mk_lt_mk.mpr
  linarith

@[simp]
theorem PRat.coe_mul (a b : ℚ+) : (a * b).val = a.val * b.val := rfl

@[simp]
theorem PRat.coe_add (a b : ℚ+) : (a + b).val = a.val + b.val := rfl

@[simp]
theorem PRat.coe_div (a b : ℚ+): (a / b).val = a.val / b.val := by rfl

@[simp]
theorem PRat.coe_pow (a: ℚ+)(b: ℕ): (a^b).val = a.val ^ b := by rfl




theorem PRat.coe_sq (k: ℚ+): IsSquare (k.val) ↔ IsSquare k := by
  constructor
  intro h
  unfold IsSquare at h
  unfold IsSquare
  obtain ⟨k, kpos⟩ := k
  obtain ⟨r, hr⟩ := h
  simp at hr
  wlog! rpos: 0 < r generalizing r with h
  have rnz: r ≠ 0 := by
    by_contra! rz
    simp[rz] at hr
    linarith

  apply lt_or_eq_of_le at rpos
  simp [rnz] at rpos
  specialize h (-r)
  rw [neg_mul_neg] at h
  specialize h hr (neg_pos.mpr rpos)
  assumption
  use ⟨r, rpos⟩
  have kk: ℚ+ := (⟨k, kpos⟩:ℚ+)
  apply Subtype.val_inj.mp
  simp
  assumption

  intro ⟨r, hr⟩
  unfold IsSquare
  use r
  rw [hr]
  simp

theorem num_or_den_zero_padicVal (a : ℚ) {p : ℕ} (hp : p.Prime) :
    padicValInt p a.num = 0 ∨ padicValNat p a.den = 0 := by
  have h := a.reduced
  contrapose! h
  apply Nat.not_coprime_of_dvd_of_dvd hp.one_lt
  simp at h
  obtain ⟨⟨h1a, h1b, h1c⟩, h2⟩ := h
  rw [← Int.dvd_natAbs] at h1c
  norm_cast at h1c
  simp at h
  obtain ⟨h1, ⟨h2a, h2b⟩⟩ := h
  assumption







snip begin
variable {f:ℚ+→ℚ+}(h:∀x y, f ((f x)^2 * y) = x^3 * f (x*y))
include f h

lemma hinj: Injective f := by
  intro x y heq
  have hx:= h x 1
  have hy := h y 1
  simp at hx hy
  nth_rw 1 [heq] at hx
  rw [hx, heq, mul_right_cancel_iff] at hy
  rwa [pow_left_inj] at hy
  decide

lemma f1: f 1 = 1 := by
  have h1:= h 1 1
  simp at h1
  apply hinj h at h1
  simp at h1
  assumption

lemma hsq : ∀x, f ((f x) ^ 2) = x ^ 3 * f x := by
  intro x
  specialize h x 1
  simp at h
  assumption

lemma fmul: ∀x y, f (x*y) = f x * f y := by
  intro x y
  have h1 := h (x*y) 1
  simp at h1
  have h2 := h x ((f y)^2)
  rw [mul_comm x] at h2
  nth_rw 2 [h] at h2
  rw [← mul_assoc, mul_comm y] at h2
  rw [mul_pow, ← h2, ← mul_pow] at h1
  clear h2
  apply hinj h at h1
  rwa [pow_left_inj] at h1
  decide

lemma fpow: ∀n:ℤ,∀x:ℚ+, (f x)^n = f (x^n) := by
  intro n x
  induction n with
    | zero => simp [f1 h]
    | succ i ih => rw [zpow_add_one, zpow_add_one, fmul h, ih]
    | pred i ih =>
      rw [zpow_sub_one, zpow_sub_one, fmul h, ih, mul_left_cancel_iff]
      suffices: f x * (f x)⁻¹ = f x * f x⁻¹
      · rwa [mul_left_cancel_iff] at this
      simp [← fmul h, f1 h]

lemma fnpow: ∀n:ℕ, ∀x:ℚ+, (f x)^n = f (x^n) := by
  intro n x
  induction n with
    | zero => simp [f1 h]
    | succ i ih => rw [pow_succ, pow_succ, fmul h, ih]

lemma sq_comm: ∀x, (f (f x))^2 = f ((f x)^2) := by
  intro x
  have h1 := h x 1
  have h0 := h x 1
  simp at h1 h0
  rwa [pow_two, fmul h (f x) (f x), ← pow_two, ← h0] at h1

lemma f_one_div: ∀x, 1 / f x = f (1/x) := by
  intro x
  rw [← inv_eq_one_div, ← zpow_neg_one, fpow h, zpow_neg_one, inv_eq_one_div]


lemma solution: ∀x, f x = 1/x := by
  intro x
  have h1 : f (x* f x)^2 = (x * f x)^3 := by
    rw [fnpow h, pow_two, fmul h, fmul h, mul_left_comm, mul_assoc, ←pow_two]
    rw [mul_pow, pow_succ' (f x), ← mul_assoc, ← mul_assoc, ← hsq h x, fnpow h, ← pow_two, mul_comm]

  have ⟨a, ha⟩: ∃a, a = x*f x := by simp
  rw [← ha] at h1
  have ha': ∀n, ∃b, b^(2^n) = a := by
    intro n
    by_cases! hn: n < 1
    simp at hn
    rw [hn]
    simp
    induction n, hn using Nat.le_induction with
    | base =>
      apply_fun (· / a^2) at h1
      rw [← div_pow, pow_succ' a, mul_div_assoc, div_self', mul_one] at h1
      use (f a / a)
      simp
      assumption
    | succ d dn hd =>
      obtain ⟨b, hb⟩ := hd
      rw [← hb, ← fnpow h, ← pow_mul, ← pow_mul, mul_comm, mul_comm (2^d), pow_mul, pow_mul] at h1
      rw [pow_left_inj (by simp: 2^d ≠ 0)] at h1
      apply_fun (· / b^2) at h1
      rw [← div_pow, pow_succ' b, mul_div_assoc, div_self', mul_one] at h1
      use (f b / b)
      rw [← hb, pow_succ, mul_comm, pow_mul, pow_left_inj (by simp: 2^d ≠ 0)]
      assumption

  have a1: a = 1 := by
    have hzero : ∀ p : ℕ, p.Prime → padicValRat p a = 0 := by
      intro p hp
      let k := padicValRat p a
      by_contra hk_ne_zero

      have h_unbounded : ∃ n : ℕ, 2 ^ n > k.natAbs := by
        use k.natAbs
        exact Nat.lt_two_pow_self

      obtain ⟨n, hn_gt⟩ := h_unbounded
      obtain ⟨b, hb_eq⟩ := ha' n

      have h_val_eq : padicValRat p (b ^ (2 ^ n)) = padicValRat p a := by
        rw [← hb_eq]
        norm_cast

      have hpi : Fact p.Prime := ⟨hp⟩
      rw [padicValRat.pow b] at h_val_eq

      have h_div : (2 ^ n : ℤ) ∣ k := by
        unfold k
        rw [← h_val_eq]
        exact Dvd.intro (padicValRat p b) rfl

      have h_le : (2 ^ n : ℤ) ≤ |k| := by
        apply Int.le_abs_of_dvd hk_ne_zero h_div

      rw [Int.abs_eq_natAbs] at h_le
      norm_cast at h_le
      linarith

    have hnumden1: ∀ (p : ℕ), Nat.Prime p → (↑(padicValInt p (a.val).num) = 0)
      ∧ ↑(padicValNat p (a.val).den) = 0 := by
        intro p hp
        specialize hzero p hp
        unfold padicValRat at hzero
        have hndz:= num_or_den_zero_padicVal (a.val) hp
        rcases hndz with hd | hd
        have hd' := hd
        rw [hd, sub_eq_zero] at hzero
        constructor
        assumption
        symm at hzero
        norm_cast at hzero
        constructor
        rw [hd, sub_eq_zero] at hzero
        norm_cast at hzero
        assumption
    by_contra! ha1'
    have anumden: a = (a.val.num:ℚ) / a.val.den := by
      norm_cast
      simp
    by_cases! hnum: a.val.num = 1
    by_cases! hden: a.val.den = 1
    rw [hnum, hden] at anumden
    norm_num at anumden
    rw [show (1:ℚ) = (⟨1, one_pos⟩:ℚ+).val by rfl] at anumden
    rw [Subtype.val_inj] at anumden
    norm_cast at anumden
    have ⟨fac, ⟨facprime, facdvd⟩⟩ := Nat.exists_prime_and_dvd hden
    have hgi: Fact fac.Prime := ⟨facprime⟩
    specialize hnumden1 fac facprime
    rw [dvd_iff_padicValNat_ne_zero (Rat.den_ne_zero a)] at facdvd
    tauto
    have apos: 0 < (a:ℚ) := by grind
    have anumpos: 0 < a.val.num := by
      rwa [← Rat.num_pos] at apos
    have anumabs: a.val.num.natAbs ≠ 1 := by
      by_contra! hhh
      grind

    have ⟨fac, ⟨facprime, facdvd⟩⟩ := Int.exists_prime_and_dvd anumabs
    rw [Int.prime_iff_natAbs_prime] at facprime
    specialize hnumden1 fac.natAbs facprime
    obtain ⟨hnump, hdenp⟩ := hnumden1
    clear hdenp
    simp at hnump
    rcases hnump with hw|hw|hw
    rw [hw] at facprime; contradiction
    linarith
    contradiction
  rw [a1, mul_comm, ← div_eq_iff_eq_mul] at ha
  symm
  assumption


snip end


determine solution_set: Set (ℚ+→ℚ+) := {fun x ↦ (1:ℚ+)/x }

theorem imo2012SLA5(f:ℚ+→ℚ+): f ∈ solution_set ↔ ∀x y, f ((f x)^2 * y) = x^3 * f (x*y):= by
  constructor
  intro h x y
  simp at h
  simp [h]
  rw [mul_rotate', mul_left_cancel_iff, inv_eq_one_div, one_div_mul_eq_div, pow_three', mul_div_assoc, div_self', ← pow_two, mul_one]
  intro h
  have sol:= solution h
  funext w
  exact sol w




end imo2010a5
