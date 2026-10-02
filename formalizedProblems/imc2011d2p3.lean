/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.PSeries
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMC 2011 Day 2 p3
https://www.imc-math.org.uk/imc2011/imc2011-day2-solutions.pdf
-/

namespace imc2011
open Real Finset

noncomputable def l:ℕ→ℝ:= fun n ↦ log (1+1/n) * log (1 + 1/(2*n)) * log (1+1/(2*n+1))


problem imc2011d2p3: ∑' n:ℕ, l (n+1) = (1/3 * (log 2)^3) := by
  let f (n:ℕ) := log ((n+1)/n)
  have hfeq: ∀n>0, f (2*n) + f (2*n+1) = f n := by
    intro m hm
    unfold f
    norm_cast
    rw [← log_mul]
    field_simp
    push_cast
    rw [add_assoc, show (1:ℝ)+1 = 2 by norm_num]
    field_simp
    norm_num
    constructor
    linarith
    lia
    grind
  have fle: ∀n > 0, f n ≤ 1/n := by
    intro n hn
    unfold f
    rw [add_div, div_self, log_le_iff_le_exp (by positivity), add_comm]
    apply add_one_le_exp
    positivity

  let g (n:ℕ) := ∑ k ∈ Finset.Ico n (2*n), (f k)^3

  have gltfn: ∀n>0, g n ≤ 1/n^2 := by
    intro n hn
    unfold g
    have i1: ∑ k ∈ Finset.Ico n (2 * n), f k ^ 3 ≤ (∑ k ∈ Finset.Ico n (2 * n), (1:ℝ)/k ^ 3) := by
      apply Finset.sum_le_sum
      intro i hi
      simp at hi
      have ipos: 0 < i := by lia
      specialize fle i ipos
      rwa [← one_div_pow, Odd.pow_le_pow (by decide)]
    apply LE.le.trans i1

    have i2:  ∑ k ∈ Finset.Ico n (2 * n), (1:ℝ)/k ^ 3 ≤  (∑ k ∈ Finset.Ico n (2 * n), ((1:ℝ)/n) ^ 3) := by
      apply Finset.sum_le_sum
      simp
      intro i hi hin
      field_simp
      rw [← div_pow, ← one_pow 3, Odd.pow_le_pow (by decide), div_le_one (by norm_cast; linarith)]
      exact_mod_cast hi

    apply LE.le.trans i2
    simp
    field_simp
    rw [show 2*n - n = n by rw [← Nat.sub_one_mul 2 n]; norm_num]

  have hg1: ∀n > 0, (1/3) * (g n - g (n+1)) = f n * f (2*n) * f (2*n + 1) := by
    intro n hn
    field_simp
    unfold g
    rw [mul_add, mul_one, show 2*n + 2 = 2*n+1+1 by norm_num, ← insert_Ico_right_eq_Ico_add_one, sum_insert,← insert_Ico_right_eq_Ico_add_one, sum_insert, ← insert_Ico_add_one_left_eq_Ico, sum_insert]
    ring_nf
    nth_rw 1 [← hfeq n hn]
    ring_nf
    rw [← add_mul, pow_two, pow_two, ← mul_assoc, ← add_mul, ← mul_add]
    rw [mul_comm n 2, add_comm 1, add_comm, hfeq n hn]
    ring_nf
    simp; lia; simp; apply add_one_le_two_mul; lia; simp; lia

  have e1: ∀n>0, l n = f n * f (2*n) * f (2*n + 1) := by
    intro n hn
    unfold l f
    push_cast
    simp only [add_div]
    field_simp

  have e2: ∑' (n : ℕ), l (n + 1) = (1/3) * ∑' (n : ℕ), (g (n+1) - g (n+2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [e1 (n+1) (by linarith), hg1 (n+1) (by linarith)]
  have gsum: Summable fun b ↦ g (b+1) := by
    have gltfn1: ∀n, g (n+1) ≤ 1/(n+1)^2 := by
      intro n
      have h1:= gltfn (n+1) (by linarith)
      push_cast at h1; assumption
    have g1pos: ∀k, 0 ≤ g (k+1) := by
      intro k
      unfold g
      apply Finset.sum_nonneg
      intro i hi
      simp at hi
      unfold f
      have ipos: (0:ℝ) < i := by norm_cast; linarith
      rw [Odd.pow_nonneg_iff (by decide), log_nonneg_iff, one_le_div ipos]
      norm_cast; lia
      positivity
    apply Summable.of_nonneg_of_le g1pos gltfn1
    have hf': (fun b ↦ ((1:ℝ) / ((b:ℕ)+1)^2)) = fun (b:ℕ) ↦ (1:ℝ)/|((b:ℝ)+1)|^((2:ℕ):ℝ) := by
      funext w
      field_simp
      rw [rpow_natCast (|↑w + 1|), sq_abs]
    rw [hf',summable_one_div_nat_add_rpow]
    norm_num
  have gsum2: Summable fun b ↦ g (b+2) := by
    have gltfn1: ∀n, g (n+2) ≤ 1/(n+2)^2 := by
      intro n
      have h1:= gltfn (n+2) (by linarith)
      push_cast at h1; assumption
    have g1pos: ∀k, 0 ≤ g (k+2) := by
      intro k
      unfold g
      apply Finset.sum_nonneg
      intro i hi
      simp at hi
      unfold f
      have ipos: (0:ℝ) < i := by norm_cast; linarith
      rw [Odd.pow_nonneg_iff (by decide), log_nonneg_iff, one_le_div ipos]
      norm_cast; lia
      positivity
    apply Summable.of_nonneg_of_le g1pos gltfn1
    have hf': (fun b ↦ ((1:ℝ) / ((b:ℕ)+2)^2)) = fun (b:ℕ) ↦ (1:ℝ)/|((b:ℝ)+2)|^((2:ℕ):ℝ) := by
      funext w
      field_simp
      rw [rpow_natCast (|↑w + 2|), sq_abs]
    rw [hf',summable_one_div_nat_add_rpow]
    norm_num
  rw [e2, mul_left_cancel_iff_of_pos (by positivity), Summable.tsum_sub, Summable.tsum_eq_zero_add]
  norm_num
  unfold g f
  simp
  norm_num
  apply gsum
  apply gsum
  apply gsum2

end imc2011
