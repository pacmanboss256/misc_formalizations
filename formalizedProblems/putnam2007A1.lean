/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
## Putnam 2007 A1
Let S be the smallest set of positive integers where

a) 2 ∈ S
b) if n^2 ∈ S, then n ∈ S
c) (n+5)^2 ∈ S

find all positive integers not in S
-/
namespace putnam2007

def conditions(S: Set ℕ):= 2 ∈ S ∧ (∀n, n^2 ∈ S → n ∈ S) ∧ (∀n ∈ S, (n+5)^2 ∈ S)

problem putnam2007A1(S: Set ℕ)(h0: 0 ∉ S)(hS: conditions S)(hmin: ∀T⊆S, ¬conditions T)
  : S = {k| 2 ≤ k ∧ ¬5 ∣ k}:= by
  obtain ⟨h2, hsq, h5⟩ := hS
  have hper: ∀n ∈ S, ∀k, n + 5*k ∈ S := by
    intro n hn k
    induction k with
    |zero =>
      simp
      specialize h5 n hn
      apply hsq at h5
      assumption
    |succ k hk =>
      rw [mul_add, ← add_assoc, mul_one]
      specialize h5 (n+5*k) hk
      apply hsq at h5
      assumption
  have h1: 1 ∉ S := by
    intro h
    let S' := S \ {1}
    have hs': S' ⊆ S := by unfold S'; simp
    apply hmin S'
    assumption
    unfold conditions S'
    constructor
    simp [h2]
    constructor
    intro k hk
    simp at hk
    obtain ⟨ksq, nk1⟩ := hk
    simp [hsq k ksq, nk1]
    intro k hk
    simp at hk
    obtain ⟨ksq, nk1⟩ := hk
    constructor
    apply h5; assumption
    simp




  ext i
  simp
  constructor
  intro mem
  constructor
  by_contra! hi
  change i < 1 + 1 at hi
  rw [Nat.lt_add_one_iff, Order.le_one_iff] at hi
  rcases hi with rfl | rfl <;> contradiction
  have hn5: ∀w, 5*w ∉ S := by
    let S' := S \ {k | ∃w, k = 5*w}
    have hS': S' ⊆ S := by grind
    specialize hmin S' hS'
    contrapose hmin
    unfold conditions
    constructor
    unfold S'
    simp [h2]
    by_contra! hw
    rw [← dvd_iff_exists_eq_mul_right] at hw
    tauto
    constructor
    intro n
    unfold S'
    simp
    intro hsq' x5
    have hx: n ≠ 5 := by
      by_contra! hx
      specialize x5 n
      rw [hx] at x5
      tauto
    apply hsq at hsq'
    simp [hsq']
    intro y hy
    specialize x5 (5*y^2)
    rw [hy] at x5
    ring_nf at x5
    tauto
    intro n
    unfold S'
    simp
    intro hn x5
    constructor
    apply h5; assumption
    contrapose x5
    simp
    simp at x5
    obtain ⟨y, hy⟩:= x5
    rw [add_sq] at hy
    have hydvd: 5 ∣ (n^2+2*n*5+5^2) := by use y
    have h5dvd: 5 ∣ n^2 := by grind
    apply Nat.Prime.dvd_of_dvd_pow (by decide) at h5dvd
    rwa [← dvd_iff_exists_eq_mul_right]

  by_contra! hi'
  rw [dvd_iff_exists_eq_mul_right] at hi'
  obtain ⟨c, hc⟩:= hi'
  specialize hn5 c
  rw [← hc] at hn5
  contradiction

  intro ⟨ge2, hdvd⟩
  have h16: 16 ∈ S := by
    apply h5 at h2
    apply h5 at h2
    change 54^2 ∈ S at h2
    suffices: 56^2 ∈ S
    apply hsq at this
    have h121: 11 ∈ S := by
      apply hsq
      specialize hper 56 this 13
      simp at hper
      assumption
    apply hper at h121
    specialize h121 1
    simp at h121
    assumption
    simp
    simp at h2
    apply hper at h2
    specialize h2 44
    assumption

  by_cases! mod1: i ≡ 1 [MOD 5]
  suffices: 6 ∈ S
  by_cases! i1: i < 5
  rw [Nat.ModEq, Nat.mod_eq_of_lt i1] at mod1; lia
  symm at mod1
  rw [Nat.modEq_iff_dvd', dvd_iff_exists_eq_mul_right] at mod1
  obtain ⟨c,hc⟩ := mod1
  have c1: 1 ≤ c := by lia
  induction c, c1 using Nat.le_induction with
    | base =>
      simp at hc; rwa [hc]
    | succ c c1 ih =>
      specialize hper 6 this c
      rw [Nat.sub_eq_iff_eq_add] at hc
      ring_nf at hc hper
      rwa [hc]
      lia
  lia
  apply hsq
  specialize hper 16 h16 4
  assumption
  suffices imod: i % 5 ∈ S
  specialize hper (i % 5) imod (i/5)
  rwa [Nat.mod_add_div] at hper
  mod_cases i % 5
  rw [Nat.modEq_zero_iff_dvd] at H; tauto; tauto
  all_goals (rw [Nat.ModEq] at H; simp at H;rw [H])
  assumption
  change 4^2 ∈ S at h16
  apply hsq at h16
  specialize hper 4 h16 1
  change 3^2 ∈ S at hper
  apply hsq at hper; assumption
  change 4^2 ∈ S at h16
  apply hsq at h16; assumption

end putnam2007
