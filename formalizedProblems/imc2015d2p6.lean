/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Topology.Algebra.Group.Defs
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMC 2015 Day 2 P6
https://www.imc-math.org.uk/imc2015/imc2015-day2-solutions.pdf
-/

namespace imc2015
open Real

noncomputable def f:ℕ→ℝ:= fun n ↦ (1:ℝ)/(√n * (n+1))

problem imc2015d2p6: ∑' n:ℕ+, f n < 2 := by
  have fpos: ∀n, 0 ≤ f (n+1) := by
    intro n
    unfold f
    positivity
  let g:ℕ→ℝ:= fun n ↦ (2/√n - 2/(√(n+1)))
  have fg: ∀n, f (n+1) < g (n+1) := by
    intro n
    let n' := n + 1
    have hn': 0 < n' := by positivity
    change f n' < g n'
    unfold f
    unfold g
    rw [← mul_lt_mul_iff_of_pos_right (by positivity: 0 < (√↑n' * ((n':ℝ) + 1))), div_mul_comm, div_self (by positivity)]
    simp
    rw [sub_mul, ← mul_assoc, div_mul_comm, div_self (by positivity)]
    simp
    rw [mul_comm (√↑n'), ← mul_assoc, div_mul_comm, mul_comm _ 2, div_sqrt, mul_assoc]
    rw [← sqrt_mul (by positivity), mul_add]
    simp
    rw [lt_sub_iff_add_lt, add_comm, ← lt_sub_iff_add_lt, add_sub_assoc, show (2:ℝ)-1 = 1 by ring_nf]
    rw [two_mul (n':ℝ), mul_comm _ (√(↑n')), add_assoc]
    nth_rw 3 [← sq_sqrt (by positivity: (0:ℝ) ≤ n')]
    nth_rw 2 [← sq_sqrt (by positivity: (0:ℝ) ≤ n'+1)]
    have h1: 2 * (√↑n' * √(↑n' + 1)) ≤  √↑n' ^ 2 + √(↑n' + 1) ^ 2 := by
      generalize  √(↑n' + 1) = a
      generalize √↑n' = b
      rw [← mul_assoc]
      apply two_mul_le_add_sq
    apply lt_or_eq_of_le at h1
    rcases h1 with lt | eq
    assumption
    ring_nf at eq
    rw [sq_sqrt (by positivity),sq_sqrt (by positivity)] at eq
    rw [← pow_left_inj₀ (by positivity) (by positivity) (by decide: 2 ≠ 0)] at eq
    ring_nf at eq
    rw [sq_sqrt (by positivity), sq_sqrt (by positivity)] at eq
    norm_cast at eq
    omega


  have fg': ∀n, f (n+1) ≤ g (n+1) := by
    intro n
    have h1 := fg n
    exact (le_of_lt h1)
  have gpos: ∀n, 0 ≤ g (n+1) := by
    intro n
    specialize fpos n
    specialize fg' n
    linarith
  suffices gsum: ∑' n:ℕ+, g n = 2
  rw [← gsum, tsum_pnat_eq_tsum_succ, tsum_pnat_eq_tsum_succ]
  apply Summable.tsum_lt_tsum_of_nonneg fpos fg' (fg 4)
  rw [tsum_pnat_eq_tsum_succ] at gsum
  contrapose gsum
  apply tsum_eq_zero_of_not_summable at gsum
  by_contra hsum
  rw [gsum] at hsum
  simp at hsum
  rw [tsum_pnat_eq_tsum_succ]
  let s:ℕ→ℝ := fun w ↦  2 / sqrt (w+1)
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg gpos]

  have gseq: (fun n ↦ ∑ i ∈ Finset.range n, g (i + 1)) = (fun n ↦ ∑ i ∈ Finset.range n, (s i - s (i+1))) := by
    funext w
    apply Finset.sum_congr rfl
    intro x hx
    unfold s g
    norm_cast

  have hfineq: (fun n ↦ ∑ i ∈ Finset.range n, (s i - s (i + 1))) = fun n ↦ (s 0 - s n) := by
    funext w
    apply Finset.sum_range_sub'

  have s0: s 0 = 2 := by
    unfold s
    norm_num
  rw [gseq,hfineq, show (2:ℝ) = (2-0) by norm_num, s0,Filter.tendsto_const_sub_iff, show (0:ℝ) = 2*0 by ring]
  unfold s
  have seq: (fun (w:ℕ)↦ 2 / √((w + 1)))= (fun (w:ℕ) ↦ 2 * (1/√(w + 1))) := by
    funext w
    ring_nf
  rw [seq]
  apply Filter.Tendsto.const_mul
  let g':ℕ→ℝ := fun n ↦ 1/((n:ℝ)+1)
  let c':ℕ→ℝ := fun n ↦ 1/(√((n:ℝ)+1))
  let h':ℕ→ℝ := fun n ↦ 1/√(n:ℝ)
  change Filter.Tendsto (c') Filter.atTop (nhds 0)
  have hlimbot: ∀n ≥ 1, g' n ≤ c' n := by
    intro n hn
    unfold g' c'
    field_simp
    rw [add_comm, sqrt_le_self_iff]
    right
    linarith
  have hlimtop: ∀ n ≥ 1, c' n ≤ h' n := by
    intro n hn
    unfold h' c'
    field_simp
    rw [sqrt_le_sqrt_iff (by positivity)]
    linarith

  have hbot: Filter.Tendsto (g') Filter.atTop (nhds 0) := by
    unfold g'
    exact tendsto_one_div_add_atTop_nhds_zero_nat

  have htop: Filter.Tendsto (h') Filter.atTop (nhds 0) := by
    unfold h'
    have h_eq : (fun (n : ℕ) => 1 / Real.sqrt (n : ℝ)) = fun (n : ℕ) => (n : ℝ) ^ (- (1 / 2) : ℝ) := by
      ext n
      by_cases hn : (n : ℝ) = 0
      · rw [hn, Real.sqrt_zero, div_zero, zero_rpow (by norm_num)]
      · rw [Real.sqrt_eq_rpow, rpow_neg (by positivity),inv_eq_one_div]
    rw [h_eq]
    refine Filter.Tendsto.comp (tendsto_rpow_neg_atTop (by norm_num)) ?_
    apply tendsto_natCast_atTop_atTop

  refine Filter.Tendsto.squeeze' hbot htop ?_ ?_
  simp; use 1
  simp; use 1
  























end imc2015
