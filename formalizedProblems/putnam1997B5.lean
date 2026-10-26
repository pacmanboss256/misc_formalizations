/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.NumberTheory.PowModTotient
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## Putnam 1997 B5
Prove that for all n ≥ 2, 2 ↑↑ n ≡  2 ↑↑ (n-1) [MOD n]
-/
namespace putnam1997
open Function



def tetrate: ℕ → ℕ
  | 0     => 1
  | n + 1 => 2 ^ (tetrate n)

lemma tet_rec: ∀k ≥ 1, tetrate k = 2^(tetrate (k-1)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rfl

lemma tet_lt: ∀k ≥ 1, tetrate (k-1) < tetrate k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp; decide
  | succ k hk ih =>
    rw [tet_rec (k+1)]
    apply Nat.lt_two_pow_self
    lia

lemma self_le_tet: ∀k, k ≤ tetrate k := by
  intro k
  induction k with
  | zero => simp
  |succ k hk=>
    rw [tet_rec]
    apply LE.le.trans_lt hk
    rw [← tet_rec]
    apply tet_lt (k+1)
    all_goals lia

lemma pow_sub_le_self_iff: ∀x, 2^x - 2 ≤  x ↔ x < 3 := by
  intro x

  constructor
  intro h
  contrapose! h
  induction x, h using Nat.le_induction with
  | base => lia
  | succ k ih =>
    have: 2 ^ k * 2 - 2 = 2*(2^k - 1):= by
      ring_nf
      rw [Nat.sub_mul]
      rfl
    rw [pow_succ,this, ← Nat.lt_sub_iff_add_lt]
    lia
  intro hx
  rw [Nat.lt_add_one_iff, Order.le_two_iff] at hx
  rcases hx with zero|one|two
  simp [zero]
  simp [one]
  simp [two]





problem Putnam1997B5 (n:ℕ)(hn: 2≤n): tetrate (n-1) ≡ tetrate (n) [MOD n] := by
  induction n using Nat.strong_induction_on with
  |h n ih =>
    by_cases! hn2: n ≤ 2
    have hn2': n = 2 := by lia
    simp [hn2']
    rfl
    clear hn
    have ⟨a, b, bodd, hab⟩ := Nat.exists_eq_two_pow_mul_odd (by positivity: n ≠ 0)
    rw [hab]
    have hcp: (2^a).Coprime b := by
      have hb: (2).Coprime b := by rwa [Nat.coprime_two_left]
      exact Nat.Coprime.pow_left a hb
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcp]
    constructor
    rw [Nat.modEq_iff_dvd', tet_rec (2 ^ a * b - 1), tet_rec]
    have e1: 2 ^ tetrate (2 ^ a * b - 1) - 2 ^ tetrate (2 ^ a * b - 1 - 1) = 2 ^ tetrate (2 ^ a * b - 1 - 1) * (2 ^ (tetrate (2 ^ a * b - 1)-tetrate (2 ^ a * b - 1 - 1))-1):=  by
      have i1:  tetrate (2 ^ a * b - 1-1) <  tetrate (2 ^ a * b - 1) := by
        apply tet_lt
        norm_num
        by_cases! hb: b = 1
        simp [hb]
        simp [hb] at hab
        rw [← hab] at hcp
        have ha: a > 0 := by
          by_contra ha'
          lia
        lia
        lia
      generalize tetrate (2 ^ a * b - 1) = w at i1
      generalize tetrate (2 ^ a * b - 1 -1 ) = w' at i1
      ring_nf
      rw [Nat.sub_mul, pow_sub_mul_pow]
      simp; lia
    rw [e1]
    apply Nat.dvd_mul_right_of_dvd
    apply Nat.pow_dvd_pow
    trans 2 ^ a * b - 1 - 1
    change a ≤ 2 ^ a * b - 2
    by_cases! ha: 3 ≤ a
    rw [← not_lt, ← pow_sub_le_self_iff] at ha
    push Not at ha
    trans 2 ^ a - 2; lia
    rw [Nat.sub_le_sub_iff_right]
    simp
    unfold Odd at bodd
    obtain ⟨k, hk⟩:= bodd
    rw [hk]; lia
    lia
    have i3: ∀q, q ≤ 2 ^ q * 3 - 2 := by
      intro q
      induction q with
      |zero=> lia
      |succ q hq=> lia
    by_cases! hb: 3 ≤ b
    trans 2^a*3 - 2
    apply i3
    apply Nat.sub_le_sub_right
    apply Nat.mul_le_mul_left
    assumption
    have hb1: b = 1 := by grind
    simp [hb1]
    rw [← Nat.le_iff_lt_add_one, Order.le_two_iff] at ha
    rcases ha with zero | one | two
    simp [zero]
    simp [one, hb1] at hab
    lia
    lia
    apply self_le_tet
    lia
    rw [← hab]; lia
    suffices hab1: 2^a*b ≥ 1
    apply tet_lt at hab1; lia; lia
    rw [tet_rec (2^a*b), Nat.ModEq,Nat.pow_totient_mod]





    --Nat.mod_two_pow_self












end putnam1997
