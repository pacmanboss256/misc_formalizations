/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Real.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 2002 A4
Find all functions f : ℝ → ℝ such that
(f(x) + f(z)) * (f(y) + f(t)) = f(xy-zt) + f(xt+yz)
for all x y z t ∈ ℝ
-/

namespace imo2002A4
open Real

determine solution_set: Set (ℝ→ℝ) := {fun _ ↦ 0, fun _ ↦ 1/2, fun x ↦ x^2}
snip begin
lemma f_zero{f:ℝ→ℝ}(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)):
  (f = fun _ ↦ 1/2) ∨ f 0 = 0 := by
  by_cases h0' : f 0 = 0
  · right; assumption
  push Not at h0'
  have : ∀x, f x = 1/2 := by
    intro x
    have h0 := h x 0 x 0
    ring_nf at h0
    apply_fun (· / 2) at h0
    rw [mul_div_assoc, mul_div_assoc] at h0
    norm_num at h0
    rw [mul_rotate, mul_assoc, mul_right_eq_self₀] at h0
    simp [h0'] at h0
    apply_fun (· / 2) at h0
    ring_nf at h0
    assumption
  left
  funext w
  specialize this w
  assumption
lemma f_mul {f: ℝ→ℝ}(h0: f 0 = 0)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)):∀x y, f x * f y = f (x*y) := by
  intro x y
  specialize h x y 0 0
  simp [h0] at h
  assumption
lemma f_even{f: ℝ→ℝ}(h0: f 0 = 0)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)):
  ∀a, f (-a) = f (a) := by
  have hxy := f_mul h0 h
  have hzt : ∀z t, f (z*t) = f (-z * t) := by
    intro z t
    specialize h 0 0 z t
    simp [h0] at h
    rw [← neg_mul] at h
    rwa [hxy] at h
  intro a
  specialize hzt a 1
  simp at hzt
  symm
  assumption

lemma f_pos{f: ℝ→ℝ}(h0: f 0 = 0)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)):
  ∀x, 0 ≤ f x := by
    intro x
    wlog! xpos : 0 ≤ x generalizing x
    · rw [← neg_zero, lt_neg] at xpos
      apply le_of_lt at xpos
      specialize this (-x) xpos
      rwa [f_even h0 h] at this
    have f_sqrt := f_mul h0 h (sqrt x) (sqrt x)
    ring_nf at f_sqrt
    have fpos := sq_nonneg (f (sqrt x))
    rw [f_sqrt] at fpos
    rwa [sq_sqrt] at fpos
    assumption

lemma f_one{f:ℝ→ℝ}(h0 : f 0 = 0)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)):
  (f = fun _ ↦ 0) ∨ f 1 = 1 := by
    by_cases h1' : f 1 = 1
    · right; assumption
    push Not at h1'
    have : ∀x, f x = 0 := by
      intro x
      have q := f_mul h0 h x 1
      simp at q
      rw [mul_right_eq_self₀] at q
      simp [h1'] at q
      assumption
    left
    funext w
    exact this w
lemma f_nonzero{f:ℝ→ℝ}(h0 : f 0 = 0)(h1: f 1 = 1)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)): ∀x ≠ 0, f x ≠ 0 := by
  intro x xnz
  have hx := f_mul h0 h x (1/x)
  rw [mul_one_div_cancel, h1] at hx
  · by_contra hf'
    rw [hf'] at hx
    simp at hx
  assumption

lemma f_posStrict {f:ℝ→ℝ}(h0 : f 0 = 0)(h1: f 1 = 1)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)): ∀x ≠ 0, f x > 0 := by
  intro x hx
  have f_nonneg := f_pos h0 h x
  have fnz := f_nonzero h0 h1 h x hx
  apply lt_or_eq_of_le at f_nonneg
  rcases f_nonneg with l | r
  · assumption
  tauto

lemma f_sq{f:ℝ→ℝ}(h0 : f 0 = 0)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)): ∀x, f x^2 = f (x^2) := by
  intro x
  nth_rw 2 [pow_two]
  rw [← f_mul h0 h x x, ← pow_two]


lemma hsq_rat{f:ℝ→ℝ}(f0 : f 0 = 0)(f1: f 1 = 1)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)): ∀q: ℚ, f q = q^2 := by
  have hsq_nat: ∀n:ℕ, f n = n^2 := by
    have hx :∀x, 2 * f x + 2 = f (x+1) + f (x-1) := by
      intro x
      specialize h x 1 1 1
      simp [f1] at h
      ring_nf at h
      rw [add_comm, mul_comm, show f (-1 + x) + f (1 + x) = f (x + 1) + f (x - 1) by ring_nf] at h
      assumption
    intro n
    induction n using Nat.twoStepInduction with
    | zero => norm_num; assumption
    | one => norm_num; assumption
    | more k hk hk1 =>
      specialize hx (k+1)
      norm_num at hx
      push_cast at hk1
      rw [hk1, hk] at hx
      ring_nf at hx
      symm at hx
      apply_fun (· - (↑k^2)) at hx
      rw [add_comm, add_sub_assoc] at hx
      simp at hx
      ring_nf at hx
      rw [add_comm] at hx
      push_cast
      rw [hx]
      ring_nf

  have hsq_int :∀n:ℤ, f n = n^2 := by
    intro n
    by_cases hn : 0 ≤ n
    · specialize hsq_nat (n.toNat)
      have hneg := Int.toNat_of_nonneg hn
      rify at hneg
      rwa [hneg] at hsq_nat
    push Not at hn
    specialize hsq_nat ((-n).toNat)
    rw [← neg_pos] at hn
    apply  le_of_lt at hn
    have hneg := Int.toNat_of_nonneg hn
    rify at hneg
    rw [hneg, f_even f0 h n] at hsq_nat
    rw [hsq_nat]
    simp
  intro q
  have ⟨a,b,hb,hq⟩: ∃a:ℤ, ∃b:ℕ, b ≠ 0 ∧ q = a/b := by
    use q.num, q.den
    norm_cast
    simp
  have hf := f_mul f0 h b (a/b)
  have lhs: (b:ℝ) * (↑a / ↑b) = ↑a := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self]
    · simp
    norm_cast
  rw [lhs] at hf
  clear lhs
  symm at hf
  by_cases hqnz : ↑a / ↑b = (0:ℚ)
  · rw [← hq] at hqnz
    rw [hqnz]
    norm_num
    assumption
  push Not at hqnz
  have abnz := f_nonzero f0 f1 h ((↑a / ↑b):ℚ)
  rify at hqnz
  simp [hqnz] at abnz
  push Not at abnz
  have heq : (f a) / (f b) = f (a / b) := by
    apply div_eq_of_eq_mul
    · have bnz := f_nonzero f0 f1 h (b:ℚ)
      norm_cast at bnz
      simp [hb] at bnz
      push Not at bnz
      assumption
    rw [mul_comm]
    assumption
  simp [hsq_int, hsq_nat] at heq
  rify at hq
  rw [← div_pow, ← hq] at heq
  symm
  assumption


lemma f_increase {f:ℝ→ℝ}(f0 : f 0 = 0)(f1: f 1 = 1)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)): ∀ x t, t ≠ 0 → f x ^ 2 < f (x^2 + t^2):= by
  intro x t ht
  by_cases hx : x = 0
  · rw [hx]
    norm_num
    simp [f0]
    have ftp := f_posStrict f0 f1 h t ht
    apply sq_pos_of_pos at ftp
    rw [f_sq f0 h] at ftp
    assumption
  push Not at hx
  have h' := h x x (-t) t
  simp [f0, f_even f0 h t] at h'
  ring_nf at h'
  rw [← h']
  have i1 : 0 ≤ f t ^ 2 := by exact sq_nonneg (f t)
  apply lt_or_eq_of_le at i1
  have ftp := f_posStrict f0 f1 h t ht
  have i2 : 0 < f x * f t := by
    rw [f_mul f0 h]
    apply f_posStrict f0 f1 h
    positivity
  have ftx := f_posStrict f0 f1 h x hx
  apply sq_pos_of_pos at ftp
  apply sq_pos_of_pos at ftx
  linarith




lemma f_mono {f:ℝ→ℝ}(f0 : f 0 = 0)(f1 : f 1 =  1)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)):
  ∀ x y: ℝ , 0 ≤ x → x < y → f x < f y := by
    intro x y xpos hxy
    have ⟨t, tpos, ht⟩ : ∃t>0, y^2 = x^2 + t^2 := by
      use sqrt (y^2 - x^2)
      rw [sq_sqrt]
      · ring_nf
        simp
        rw [sq_lt_sq₀]
        · linarith
        · assumption
        linarith
      rw [sub_nonneg, sq_le_sq₀]
      · linarith
      · assumption
      linarith

    have fx := f_pos f0 h x
    have fy := f_posStrict f0 f1 h y (by linarith : y ≠ 0)
    have fsq := f_increase f0 f1 h x t tpos.ne'
    rw [← ht, ← f_sq f0 h y, sq_lt_sq₀] at fsq
    · assumption
    · assumption
    linarith






lemma hsq_real{f:ℝ→ℝ}(f0 : f 0 = 0)(f1 : f 1 =  1)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)):
  ∀ x: ℝ, x ≥ 0 → f x = x^2 := by
    intro x xpos
    by_cases hz : x = 0
    · rw [hz]
      norm_num;assumption
    push Not at hz
    by_cases! xi : ¬Irrational x
    · have ⟨q, hq⟩ := exists_rat_of_not_irrational xi
      rw [hq]
      apply hsq_rat f0 f1 h
    have f_pos := f_posStrict f0 f1 h x hz
    by_contra! hx
    by_cases! hf : f x > x^2
    · have he : ∃ε > 0, f x = x^2 + ε := by
        use (f x - x^2)
        simp
        lia
      obtain ⟨ε, epos, hε⟩ := he
      have hbtw: x < sqrt (x^2 + ε) := by
        nth_rw 1 [← sqrt_sq xpos]
        apply sqrt_lt_sqrt (sq_nonneg x)
        lia
      have ⟨r, hl, hr⟩ := exists_rat_btwn hbtw
      have fr := hsq_rat f0 f1 h r
      have frx := f_mono f0 f1 h x r xpos hl
      rw [hε, fr] at frx
      rw [← sq_lt_sq₀, sq_sqrt] at hr
      any_goals linarith
    apply lt_or_eq_of_le at hf
    simp [hx] at hf
    have he : ∃ε < 0, f x = x^2 + ε := by
      use (f x - x^2)
      simp
      lia
    obtain ⟨ε, eneg, hε⟩ := he
    have hbtw: sqrt (x^2 + ε) < x := by
      nth_rw 2 [← sqrt_sq xpos]
      apply sqrt_lt_sqrt
      · linarith
      linarith

    have ⟨r, hl, hr⟩ := exists_rat_btwn hbtw
    have rpos : (0:ℝ) ≤ r := by
      have x2e : x^2 + ε > 0 := by linarith
      have sp := sqrt_pos_of_pos x2e
      linarith
    have fr := hsq_rat f0 f1 h r
    have frx := f_mono f0 f1 h r x rpos hr
    rw [hε, fr] at frx
    rw [← sq_lt_sq₀, sq_sqrt] at hl
    any_goals linarith
    apply sqrt_nonneg

theorem hsq {f:ℝ→ℝ}(f0 : f 0 = 0)(f1 : f 1 =  1)(h: ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z)):
  ∀ x: ℝ, f x = x^2 := by
  intro x
  by_cases! hx : 0 ≤ x
  · exact hsq_real f0 f1 h x hx
  apply neg_pos_of_neg at hx
  apply le_of_lt at hx
  have hf := hsq_real f0 f1 h (-x) hx
  rw [f_even f0 h] at hf
  simp at hf
  assumption



snip end

theorem imo2002SLA4 (f:ℝ→ℝ): f ∈ solution_set ↔ ∀x y z t, (f x + f z) * (f y + f t) = f (x*y - z*t) + f (x*t + y*z) := by
  simp
  rw [inv_eq_one_div]
  constructor
  · intro h x y z t
    rcases h with h | h | h
    · simp [h]
    · simp [h]
      norm_num
    simp [h]
    ring_nf
  intro h
  have f_zero := f_zero h
  rcases f_zero with h | f0
  · right; left; assumption
  have f_one := f_one f0 h
  rcases f_one with h | f1
  · left; assumption
  have sq := hsq f0 f1 h
  right; right
  funext w
  specialize sq w
  assumption
end imo2002A4
