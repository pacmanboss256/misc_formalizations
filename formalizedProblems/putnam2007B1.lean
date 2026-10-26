/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Algebra.Polynomial.Inductions
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## Putnam 2007 B1
Let f be a (nonconstant) polynomial with positive integer coefficients
show f(n) divides f (f(n)+1) iff n=1
-/

namespace putnam2007
open Nat
variable{d:ℕ}(hd: 0 < d)(f:ℕ→ℕ){a : Fin (d+1)→ ℕ}(ha: ∀i: Fin (d+1), 0 < a i)(hf: ∀n, f n = ∑ i: Fin (d+1), ((a i) * n^(i.val)))
include d hd f a ha hf

omit f hf in
lemma term_lt_sum: ∀i, a i < ∑ x, a x := by
  intro i
  suffices: ∃j, j ≠ i
  obtain ⟨j, hj⟩ := this
  apply Finset.single_lt_sum hj
  simp; simp; apply ha; lia
  by_cases! hi: i = 0
  use 1; simp [hi]; lia
  use 0; simp; lia
omit f hf in
lemma mod_add_one_pow: ∀i, (a i * (∑ x, a x + 1) ^ (i.val) % ∑ x, a x) = a i := by
  intro i
  rw [mul_mod, pow_mod]
  simp
  have i1:  1 < ∑ x, a x := by
    apply LE.le.trans_lt (by apply ha: 1 ≤ a 0)
    apply term_lt_sum hd
    assumption
  rw [mod_eq_of_lt i1]
  simp
  rw [mod_eq_of_lt]
  apply term_lt_sum hd
  assumption





problem putnam2007b1(n: ℕ)(hn: 0 < n):
  n = 1 ↔ f n ∣ f (f n+1) := by
  constructor
  intro hn
  simp [hn]
  rw [hf]
  simp
  rw [hf, Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod]
  simp [mod_add_one_pow hd ha]
  intro h
  by_contra! h1
  have hn': 1 < n := by lia
  rw [hf, hf, Nat.dvd_iff_mod_eq_zero] at h
  let w := ∑ i, a i * n ^ (i.val)
  have w1: 1 < w := by
    apply LE.le.trans_lt (by apply ha: 1 ≤ a 0)
    unfold w
    trans ∑ i, a i
    apply term_lt_sum; lia; assumption
    apply Finset.sum_lt_sum
    intro i hi
    norm_cast
    apply Nat.le_mul_of_pos_right
    apply pow_pos
    lia
    use 1
    simp
    rwa [mod_eq_of_lt (by lia),Nat.lt_mul_iff_one_lt_right, pow_one]
    apply ha

  change (∑ i, (a i) * ((w + 1) ^ (i.val))) % w = 0 at h
  rw [Finset.sum_nat_mod] at h
  have wa: ∀i, a i < w := by
    intro i
    unfold w
    trans ∑ i, a i
    apply term_lt_sum; lia; assumption
    apply Finset.sum_lt_sum
    intro i hi
    norm_cast
    apply Nat.le_mul_of_pos_right
    apply pow_pos
    lia
    use 1
    simp
    rwa [mod_eq_of_lt (by lia),Nat.lt_mul_iff_one_lt_right, pow_one]
    apply ha
  conv at h=>
    lhs; lhs; rhs;
    ext i
    rw [mul_mod, pow_mod]
    simp
    rw [mod_eq_of_lt w1]
    simp [mod_eq_of_lt (by apply wa: a i < w)]
  change (∑i, a i) % w = 0 at h
  unfold w at h
  apply dvd_of_mod_eq_zero at h
  have sumpos: 0 < (∑ i, a i) := by
    apply Finset.sum_pos
    simp [ha]
    simp
  suffices: (∑ i, a i) < (∑ i, a i * n^(i.val))
  have i2:= not_dvd_of_pos_of_lt sumpos this
  tauto
  apply Finset.sum_lt_sum
  intro i hi
  apply Nat.le_mul_of_pos_right
  apply pow_pos; positivity
  use 1
  simp
  rwa [mod_eq_of_lt (by lia),Nat.lt_mul_iff_one_lt_right, pow_one]
  apply ha


end putnam2007
