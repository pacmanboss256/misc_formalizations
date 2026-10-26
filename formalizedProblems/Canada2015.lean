/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Algebra.Order.Positive.Ring
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

namespace p1

/-
(n-1)^2< f(n)f(f(n)) < n^2+n for 0 < n
-/
problem Canada2015(f:ℕ+→ℕ+): f = id ↔ (∀n:ℕ+, ((n:ℕ)-1)^2 < f n * f (f n) ∧ f n * f (f n) < n^2 + n):= by
  constructor
  intro eqid n
  simp [eqid]
  constructor
  ring_nf
  rw [Nat.pow_lt_pow_iff_left (by positivity)]
  norm_num
  rw [pow_two]
  apply PNat.lt_add_right
  intro h
  rw [forall_and] at h
  obtain ⟨h1, h2'⟩:= h
  have h2: ∀ (x : ℕ+), f x * f (f x) < x * (x+1) := by
    intro x
    specialize h2' x
    suffices: x^2 + x = x * (x+1)
    lia
    ring
  clear h2'
  funext w
  simp
  induction w using PNat.caseStrongInductionOn with
  | hz =>
    specialize h2 1
    norm_num at h2
    rw [show (1:ℕ+) + 1 = 2 by norm_cast] at h2
    apply PNat.eq_one_of_lt_two at h2
    rw [← PNat.coe_inj, PNat.mul_coe] at h2
    apply Nat.eq_one_of_mul_eq_one_right at h2
    norm_cast at h2
  | hi k ih =>
    have ⟨a, ha⟩: ∃a, f (k+1) = a := by simp
    rw [ha]
    rcases (lt_trichotomy a (k+1)) with lt | rfl | gt
    have hk1:= h1 (k+1)
    rw [PNat.add_coe] at hk1
    norm_num at hk1
    norm_cast at hk1
    have hk2 := h2 (k+1)
    rw [ha] at hk1 hk2
    rw [PNat.lt_add_one_iff] at lt
    specialize ih a lt
    rw [ih, ← pow_two, ← PNat.coe_lt_coe, PNat.pow_coe, PNat.pow_coe, Nat.pow_lt_pow_iff_left (by decide)] at hk1
    rw [← PNat.coe_le_coe] at lt
    lia; rfl
    have hk2 := h2 (k+1)
    rw [ha] at hk2
    have i1: f a < k+1+1 := by
      by_contra! i1
      have i2:= mul_lt_mul_of_le_of_lt i1 gt
      apply le_of_lt at i2
      apply not_le_of_gt at hk2
      rw [mul_comm, mul_comm a] at hk2
      tauto

    have hk1:= h1 (k+1)
    rw [PNat.add_coe] at hk1
    norm_num at hk1
    rw [ha] at hk1
    rw [PNat.lt_add_one_iff, le_iff_eq_or_lt] at i1
    rcases i1 with eq | lt
    nth_rw 1 [←eq] at hk2
    rw [mul_comm a, mul_lt_mul_iff_left, PNat.lt_add_one_iff] at hk2
    apply not_le_of_gt at gt
    contradiction
    rw [PNat.lt_add_one_iff] at lt
    have iha:= ih (f a) lt
    have hk2':= h2 a
    have hk1':= h1 a
    rw [iha] at hk2' hk1'
    have i3: ((a:ℕ) - 1) ^ 2 < k^2 := by
      apply LT.lt.trans_le hk1'
      rw [← pow_two, Nat.pow_le_pow_iff_left (by decide)]
      norm_cast

    rw [Nat.pow_lt_pow_iff_left (by decide), Nat.sub_lt_iff_lt_add] at i3
    norm_cast at i3
    grind
    lia

/-
(n-1)^2< f(n)f(f(n)) < n^2+n for 0 < n
-/

end p1
