/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
## IMO Shortlist 1997 17
Find all pairs a,b of positive integers that satisfy the equation a^(b^2) = b^a
-/

namespace imo1997SL17
open Real
def good (a b:ℕ): Prop := a^(b^2)= b ^ a

determine solution_set: Set (ℕ × ℕ):= {(1,1), (16,2), (27,3)}

snip begin

lemma pow_four_lt_two_pow: ∀x ≥ 17, x^4 < 2^x := by
  intro x hx
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ k ik hk =>
    suffices: (k+1)^4 < 2*k^4
    rw [← Nat.mul_lt_mul_left (by lia: 0 < 2)] at hk
    rw [pow_succ 2, mul_comm]
    linarith
    ring_nf
    rw [mul_two, Nat.add_lt_add_iff_right]
    trans k * (1 + k + k * 6 + k ^ 2 * 4); nlinarith
    rw [show k^4 = k^(3+1) by norm_num, pow_succ' k 3, Nat.mul_lt_mul_left]
    trans k * (8+4*k); lia; rw [pow_three, Nat.mul_lt_mul_left]
    trans 5*k; lia; rw [Nat.mul_lt_mul_right]; lia
    all_goals positivity

lemma pow_nine_lt_three_pow: ∀x ≥ 28, x^9 < 3^x := by
  intro x hx
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ k ik hk =>
    suffices: (k+1)^9 < 3*k^9
    rw [← Nat.mul_lt_mul_left (by lia: 0 < 3)] at hk
    rw [pow_succ 3, mul_comm]
    linarith
    ring_nf
    rw [show k^9*3 = k^9*2 + k^9 by ring_nf, Nat.add_lt_add_iff_right]
    trans k^2 * (9*k^6 + 36*k^5 + 84*k^4 + 126 * k^3 + 126 * k^2 + 84 * k + 36 + k); nlinarith
    rw [show k^9 = k^2 * k^7 by ring, mul_assoc, Nat.mul_lt_mul_left]; ring_nf
    trans k*(87 + k * (5*k) + k ^ 2 * 126 + k ^ 3 * 84 + k ^ 4 * 36 + k ^ 5 * 9); nlinarith
    rw [show k^7 = k * k^6 by ring, mul_assoc, Nat.mul_lt_mul_left]; ring_nf
    trans k^2 * (4 + 131 + k * 84 + k ^ 2 * 36 + k ^ 3 * 9); nlinarith
    rw [show k^6 = k^2 * k^4 by ring, mul_assoc, Nat.mul_lt_mul_left]; ring_nf
    trans k^2 * (40 + k * 9); nlinarith
    rw [show k^4 = k^2 * k^2 by ring, mul_assoc, Nat.mul_lt_mul_left]; ring_nf
    trans k*11; nlinarith; rw [pow_two, mul_assoc, Nat.mul_lt_mul_left]; ring_nf; linarith
    all_goals positivity
snip end

theorem imo1997SLN17(a b:ℕ)(ha: 0 < a)(hb: 0 < b): (a,b) ∈ solution_set ↔ (a^(b^2) = b^a) := by
  constructor
  intro h
  simp at h
  rcases h with i | i | i <;> simp [i]
  intro h
  have h' := h
  by_cases! ha1: a ≤ 1
  rw [show a = 1 by linarith] at h
  simp at h
  simp; left
  simp [h, show a = 1 by linarith]
  have hlog:= h
  have habne: b ≠ a := by
    by_contra! hab'
    rw [hab', Nat.pow_right_inj ha1] at h
    apply eq_zero_or_one_of_sq_eq_self at h
    rcases h with i | i <;> linarith
  rify at hlog
  apply_fun logb a at hlog
  simp [logb_pow] at hlog
  rw [logb_self_eq_one] at hlog
  simp at hlog
  symm at hlog
  rw [mul_comm, ← eq_div_iff_mul_eq] at hlog
  have ⟨m,n, npos, mncoprime, hmn⟩: ∃m n:ℕ, 0 < n ∧ m.Coprime n ∧ b = (a:ℝ)^((m:ℝ)/(n:ℝ)) := by
    have ⟨w, hw⟩: ∃w:ℚ, w = (b^2:ℝ) / (a:ℝ) := by
      use b^2/a
      norm_num
    rw [←hw, logb_eq_iff_rpow_eq] at hlog
    have ⟨m, hm⟩: ∃m:ℕ, m = w.num := by
      have wpos: (0:ℝ) < w := by
        rw [hw, div_pos_iff]
        left; simp [ha]
        rw [sq_pos_iff]
        norm_num
        linarith
      norm_cast at wpos
      use w.num.natAbs
      simp
      linarith
    have hm': m = w.num.natAbs := by
      have wpos: (0:ℚ) < w := by
        rify
        rw [hw, div_pos_iff]
        left; simp [ha]
        rw [sq_pos_iff]
        norm_num
        linarith
      zify
      rw [← Rat.num_pos] at wpos
      apply  le_of_lt at wpos
      rw [hm, abs_of_nonneg wpos]
    use m, w.den
    have hw': (w:ℝ) = (↑w.num / ↑w.den) := by
      nth_rw 1 [← Rat.num_div_den w]
      norm_cast
    constructor
    simp [Rat.den_pos]
    constructor
    have hrat := Rat.isCoprime_num_den w
    rw [← hm] at hrat
    norm_cast at hrat
    symm
    have hm' := hm
    rify at hm'
    rwa [hm',← hw']
    exact_mod_cast ha
    norm_cast; lia
    exact_mod_cast hb
  have hm: m = 1 := by
    have hr:= h
    rify at hr
    rw [← rpow_natCast, ← rpow_natCast] at hr
    push_cast at hr
    rw [hmn, ← rpow_mul, rpow_right_inj, ← rpow_natCast, ← rpow_mul, mul_comm] at hr
    by_contra! hm'
    apply_fun (· ^ (n:ℝ)) at hr
    have npos' := ne_of_gt npos
    rify at npos'
    rw [← rpow_mul, mul_rpow, mul_assoc, div_mul_comm, div_self npos'] at hr
    simp at hr
    symm at hr
    have ha' := ha
    rify at ha'
    simp [← rpow_natCast] at hr
    by_cases! hle: 2*m ≤ n
    rw [← div_eq_iff_mul_eq, ← rpow_sub ha',← inv_mul_eq_one₀, ← rpow_neg, neg_sub] at hr
    push_cast at hr
    have ⟨j, hj⟩: ∃j:ℕ, j = (a:ℝ) ^ ((n:ℝ) - 2 * ↑m) := by
      norm_cast
      simp
    rw [← hj] at hr
    simp at hr
    rw [div_pow] at hr
    field_simp at hr
    norm_cast at hr
    have mpos: 0 < m := by
      by_contra! hmpos
      simp at hmpos
      rify at hmpos
      simp [hmpos] at hmn
      simp [hmn] at h
      linarith
    have hn: 1 < n := by linarith
    have mndvd: m ∣ n := by
      rw [mul_comm] at hr
      apply Dvd.intro at hr
      norm_cast at npos'
      rwa [Nat.pow_dvd_pow_iff npos'] at hr

    have hmn1:= Nat.Coprime.eq_one_of_dvd mncoprime mndvd
    contradiction; any_goals positivity
    rw [← div_eq_iff_mul_eq, ← rpow_sub ha'] at hr
    apply le_of_lt at hle
    push_cast at hr
    have ⟨j, hj⟩: ∃j:ℕ, j = (a:ℝ) ^ (((2*m):ℝ) - ↑n) := by
      norm_cast
      simp
    push_cast at hj
    have hr' := hr
    rw [← hj] at hr
    simp at hr
    rw [div_pow] at hr
    field_simp at hr
    norm_cast at hr
    have mpos: 0 < m := by
      by_contra! hmpos
      simp at hmpos
      rify at hmpos
      simp [hmpos] at hmn
      simp [hmn] at h
      linarith
    have mndvd: n ∣ m := by
      rw [mul_comm] at hr
      apply Dvd.intro at hr
      norm_cast at npos'
      rwa [Nat.pow_dvd_pow_iff npos'] at hr
    rw [Nat.coprime_comm] at mncoprime
    have hmn1:= Nat.Coprime.eq_one_of_dvd mncoprime mndvd
    simp [hmn1] at hmn
    norm_cast at hmn
    rw [hmn, ← pow_mul, ← pow_mul, Nat.pow_right_inj ha1] at h
    have h2: m*2 = (2*m - 1) + 1 := by
      rw [Nat.sub_add_cancel, mul_comm]
      linarith
    rw [h2, pow_succ, Nat.mul_right_cancel_iff] at h
    have hmpow: m < a^m := by exact Nat.lt_pow_self ha1
    have hm'': 1 < m := by grind
    have hmpow2: a^m < a^(2*m-1) := by
      simp [Nat.pow_lt_pow_iff_right ha1]
      linarith
    rw [h] at hmpow2
    linarith
    positivity
    positivity
    norm_cast
    linarith
  have npos':= npos
  rify at npos'
  have apos' := ha
  rify at apos'
  have bpos' := hb
  rify at bpos'
  rw [hm] at hmn
  norm_cast at hmn
  rw [← rpow_left_inj (le_of_lt bpos') (le_of_lt (rpow_pos_of_pos apos' ((1:ℝ) / ↑n))) (ne_of_gt npos')] at hmn
  rw [← rpow_mul, div_mul_comm, div_self, mul_one, rpow_one] at hmn
  norm_cast at hmn
  symm at hmn
  nth_rw 1 [hmn] at h
  have hb1: 1 < b := by
    by_contra! hb1'
    have hb1' : b = 1 := by grind
    simp [hb1'] at h'
    linarith
  rw [← pow_mul, Nat.pow_right_inj, hmn] at h
  by_cases! hn2: n < 2
  have hn2': n = 1 := by grind
  simp [hn2'] at h
  apply eq_zero_or_one_of_sq_eq_self at h
  grind
  symm at h
  apply Nat.div_eq_of_eq_mul_left (by positivity) at h
  have i1: b^(n-2) = b^n / b^2 := by
    rw [show n-2 = n - 1 - 1 by grind, Nat.pow_sub_one (ne_of_gt hb), Nat.pow_sub_one (ne_of_gt hb)]
    rw [Nat.div_div_eq_div_mul, pow_two]
    lia
    lia

  rw [←i1] at h
  have hb4: b < 4 := by
    by_contra! hb4'
    have h4: ∀t ≥ 3, b^(t-2) > t := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base =>
        norm_num
        lia
      | succ k kt hk =>
        have i2: k + 1 - 2 = k - 2 + 1 := by grind
        rw [i2, pow_succ]
        trans k*b
        apply LT.lt.gt
        rw [Nat.mul_lt_mul_right (by positivity)]
        apply GT.gt.lt
        assumption
        apply LT.lt.gt
        have i3:= add_one_le_two_mul (by linarith: 1 ≤ k)
        suffices: 2*k < b*k
        linarith
        rw [Nat.mul_lt_mul_right (by positivity)]
        lia
    by_cases! hn': n ≥ 3
    specialize h4 n hn'
    lia
    have hn2': n = 2 := by grind
    simp [hn2'] at h
  have hbopt: b = 2 ∨ b = 3 := by grind
  rcases hbopt with two | three
  simp [two] at h'
  have ha': a = 16 := by
    have altrich:= lt_trichotomy a 16
    rw [show 16 = 15 + 1 by norm_num] at altrich
    rcases altrich with lt | rfl | gt
    apply Nat.le_of_lt_add_one at lt
    have ha2': 2 ≤ a := by grind
    have hafin: a ∈ Finset.Icc 2 15 := by grind
    fin_cases hafin <;> simp at h'
    rfl
    apply Nat.add_one_le_of_lt at gt
    simp at gt
    have h4:= pow_four_lt_two_pow a gt
    linarith
  simp; right; left; exact ⟨ha', two⟩
  simp [three] at h'
  have ha': a = 27 := by
    have altrich:= lt_trichotomy a 27
    rw [show 27 = 26 + 1 by norm_num] at altrich
    rcases altrich with lt | rfl | gt
    apply Nat.le_of_lt_add_one at lt
    have ha2': 2 ≤ a := by grind
    have hafin: a ∈ Finset.Icc 2 26 := by grind
    fin_cases hafin <;> simp at h'
    rfl
    apply Nat.add_one_le_of_lt at gt
    simp at gt
    have h4:= pow_nine_lt_three_pow a gt
    linarith
  simp; right; right; exact ⟨ha', three⟩
  all_goals norm_cast <;> linarith

end imo1997SL17
