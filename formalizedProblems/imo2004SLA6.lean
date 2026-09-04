/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic

public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 2004 A6
Find all functions f: ℝ → ℝ such that
f(x^2+y^2+2f(xy))=(f(x+y))^2 for all x y ∈ ℝ
-/

namespace imo2004a6
open Real Function
determine solution_set : Set (ℝ→ℝ) := {f | f = id ∨ f = 0 ∨ (∃X<(-2/3), ∀ x, (if x < X then f x = -1 else f x = 1))}
snip begin
lemma f_sq_even(f: ℝ→ℝ)(h: ∀x y, f (x^2 + y^2 + 2*f (x*y)) = (f (x+y))^2):∀x, f x ^2 = f (-x)^2 := by
  intro x
  have h1 := h x 0
  have h2 := h (-x) 0
  simp at h1 h2
  rw [h1] at h2
  assumption
lemma f_0_pos(f: ℝ→ℝ)(h: ∀x y, f (x^2 + y^2 + 2*f (x*y)) = (f (x+y))^2): 0 ≤ f 0 := by
  let c := 2*f 0
  have h0: ∀x, f (x^2 + c) = f x ^2 := by
    intro x
    specialize h x 0
    simp at h
    assumption
  have c_pos : 0 ≤ c := by
    by_contra hf
    have ⟨z, hz⟩: ∃z, z^2 = -c := by
      use sqrt (|c|)
      simp
      push Not at hf
      apply le_of_lt at hf
      assumption
    have h1 := h0 z
    rw [hz] at h1
    simp at h1
    have hec : f 0 = c * (1/2) := by
      dsimp [c]
      ring_nf
    have i1 : 0 ≤ f 0 := by
      rw [h1]
      apply sq_nonneg
    rw [hec] at i1
    field_simp at i1
    norm_num at i1
    tauto
  linarith

lemma f_x_nonneg(f: ℝ→ℝ)(h: ∀x y, f (x^2 + y^2 + 2*f (x*y)) = (f (x+y))^2):∃M, ∀x ≥ M, 0 ≤ f x := by
  use 2 * f 0
  intro x hx
  let c := 2 * f 0
  change x ≥ c at hx
  have hf0 := f_0_pos f h
  have xpos : 0 ≤ x := by linarith
  have ⟨y, hy⟩ : ∃y:ℝ, x = y^2 + c := by
    use sqrt (x - c)
    rw [sq_sqrt]
    · simp
    linarith
  specialize h y 0
  simp at h
  rw [← hy] at h
  rw [h]
  apply sq_nonneg


lemma param(f:ℝ→ℝ):(∀x y, f (x^2 + y^2 + 2 * f (x*y)) = (f (x+y))^2) ↔ (∀a b, 4 * b ≤ a^2 → f (a^2 + 2 * f b - 2*b) = f a ^ 2) := by
  constructor
  · intro h a b hab
    specialize h ((a + sqrt (a^2 - 4*b))/2) ((a - sqrt (a^2 - 4*b))/2)
    ring_nf at h
    field_simp at h
    rw [sq_sqrt] at h
    · ring_nf at h
      rw [add_sub_right_comm]
      ring_nf
      assumption
    linarith
  intro h x y
  specialize h (x+y) (x*y)
  have h4 := four_mul_le_sq_add x y
  rw [← mul_assoc] at h
  simp [h4] at h
  ring_nf at h
  rwa [mul_comm]



lemma inj_id(f: ℝ→ℝ)(h: ∀x y, f (x^2 + y^2 + 2*f (x*y)) = (f (x+y))^2): Injective f → f = id := by
  intro inj
  rw [param f] at h
  have hc: ∀r, f r = r + f 0 := by
    intro r
    have ⟨x, hx⟩ : ∃x:ℝ, 4*r ≤ x^2 := by
      use (1+2*r)
      ring_nf
      nlinarith
    have hr := h x r hx
    have h0 := h x 0 (by norm_num; apply sq_nonneg x)
    rw [← h0] at hr
    norm_num at hr h0
    apply inj at hr
    rw [add_sub_assoc, add_left_cancel_iff] at hr
    field_simp at hr
    apply eq_add_of_sub_eq' at hr
    assumption
  have h0 : f 0 = 0 := by
    by_cases! hf0 : f 0 = 0
    · assumption
    have hpick: ∀b:ℝ, ∃a:ℝ, 4*b ≤ a^2 := by
      intro b
      use (2*b + 1)
      ring_nf
      nlinarith
    have hx3 := h 4 2
    have hx2 := h 5 2
    norm_num at hx2 hx3
    nth_rw 3 [hc] at hx2 hx3
    rw [hc, hc] at hx2 hx3
    ring_nf at hx2 hx3
    rw [add_assoc, add_left_cancel_iff] at hx3 hx2
    rw [hx2, add_right_cancel_iff] at hx3
    simp at hx3
    contradiction
  funext w
  specialize hc w
  rw [h0] at hc
  simp at hc
  simp
  assumption






lemma exists_const(f: ℝ→ℝ)(h: ∀x y, f (x^2 + y^2 + 2*f (x*y)) = (f (x+y))^2)(hi: ¬ Injective f): ∃K, ∀x ≥ K, ∃C, f x = C := by
  rw [not_injective_iff] at hi
  obtain ⟨r, s, frs, rnes⟩ := hi
  wlog hrs : r > s generalizing r s with hrsg
  push Not at hrs
  apply lt_or_eq_of_le at hrs
  simp [rnes] at hrs
  specialize hrsg s r frs.symm rnes.symm hrs
  assumption
  have ⟨M₀, f_nonneg⟩ := f_x_nonneg f h


  have fsq_eq: ∃(M₁:ℝ), M₁≥2 ∧ M₁ > 2*|r| + 2 ∧ M₁ > 2*|s|+2 ∧ ∀x≥M₁, f (sqrt (x+r*2)) = f (sqrt (x+s*2)) := by
    use (M₀^2 + 100*|r| + 100 * |s| + 2)
    constructor
    by_cases! hr0 : r = 0
    have sp: 0 < 100 * |s| := by
      have s1 := abs_nonneg s
      apply lt_or_eq_of_le at s1
      rcases s1 with h1 | h1
      linarith
      symm at h1
      rw [abs_eq_zero, ← hr0] at h1
      tauto
    simp
    positivity

    have sp: 0 < 100 * |r| := by
      have s1 := abs_nonneg r
      apply lt_or_eq_of_le at s1
      rcases s1 with h1 | h1
      linarith
      symm at h1
      rw [abs_eq_zero] at h1
      tauto
    simp
    positivity

    constructor
    by_cases! hr0: r = 0
    have sp: 0 < 100 * |s| := by
      have s1 := abs_nonneg s
      apply lt_or_eq_of_le at s1
      rcases s1 with h1 | h1
      linarith
      symm at h1
      rw [abs_eq_zero, ← hr0] at h1
      tauto
    rw [← hr0] at sp
    suffices h0 : 0 ≤  M₀^2 + 100 * |r|
    grind
    positivity
    suffices h0 : 0 ≤  M₀^2 + 100 * |s|
    grind
    positivity
    constructor
    by_cases! hr0: s = 0
    have sp: 0 < 100 * |r| := by
      have s1 := abs_nonneg r
      apply lt_or_eq_of_le at s1
      rcases s1 with h1 | h1
      linarith
      symm at h1
      rw [abs_eq_zero, ← hr0] at h1
      tauto
    rw [← hr0] at sp
    suffices h0 : 0 ≤  M₀^2 + 100 * |s|
    grind
    positivity
    suffices h0 : 0 ≤  M₀^2 + 100 * |r|
    grind
    positivity

    intro x hxr
    have ir1 : 2 * |r| ≤ x := by
      trans 100 * |r|
      apply mul_le_mul_of_nonneg_right
      norm_num
      positivity
      trans  M₀ ^ 2 + 100 * |r| + 100 * |s| + 2
      rw [add_assoc, add_rotate, add_assoc]
      apply le_add_of_nonneg_right
      positivity
      assumption
    have is1 : 2 * |s| ≤ x := by
      trans 100 * |s|
      apply mul_le_mul_of_nonneg_right
      norm_num
      positivity
      trans  M₀ ^ 2 + 100 * |r| + 100 * |s| + 2
      rw [add_assoc, ←add_rotate, add_assoc, add_assoc]
      apply le_add_of_nonneg_right
      positivity
      assumption
    have h' := h
    rw [param f] at h
    have ir : 4 * r ≤ x + 2 * r := by
      suffices i1: 2 * r ≤ x
      linarith
      trans 100 * |r|
      grind
      trans  M₀ ^ 2 + 100 * |r| + 100 * |s| + 2
      rw [add_assoc, add_rotate, add_assoc]
      apply le_add_of_nonneg_right
      positivity
      assumption
    have is : 4 * s ≤ x + 2 * s := by linarith
    have hr := h (sqrt (x + 2*r)) r
    have hs := h (sqrt (x + 2*s)) s
    rw [sq_sqrt] at hr hs
    simp [ir] at hr
    simp [is] at hs
    ring_nf at hr hs
    rw [frs, hs] at hr
    have i1 : M₀ ≤ √(x + 2*r) := by
      by_cases! hm0: M₀ < 0
      trans 0
      linarith
      apply sqrt_nonneg
      rw [le_sqrt]
      trans  M₀ ^ 2 + 100 * |r| + 100 * |s| + 2 + 2 * r
      rw [add_assoc, add_assoc, add_assoc]
      apply le_add_of_nonneg_right
      rw [← add_assoc, ← add_comm, ← add_assoc]
      suffices i2 : 0 ≤ 2 + 2 * r + 100 * |r|
      positivity
      rw [show (100:ℝ) = 2 * 50 by norm_num, mul_assoc, add_assoc, ← mul_add]
      nth_rw 1 [← mul_one 2]
      rw [← mul_add]
      simp
      rw [← neg_le_iff_add_nonneg']
      trans 0
      norm_num
      rw [←neg_le_iff_add_nonneg']
      trans |r|
      apply neg_le_abs
      have i0 : 0 ≤ |r| := by positivity
      linarith
      rw [add_le_add_iff_right]
      assumption
      assumption
      rw [add_comm, ← neg_le_iff_add_nonneg',← neg_mul, neg_mul_comm]
      trans 2 * |r|
      field_simp
      apply neg_le_abs
      assumption
    have i2 : M₀ ≤ √(x + 2*s) := by
      by_cases! hm0: M₀ < 0
      trans 0
      linarith
      apply sqrt_nonneg
      rw [le_sqrt]
      trans  M₀ ^ 2 + 100 * |r| + 100 * |s| + 2 + 2 * s
      rw [add_assoc, add_assoc, add_assoc]
      apply le_add_of_nonneg_right
      rw [← add_assoc, ← add_comm, ← add_assoc, add_assoc]
      nth_rw 3 [add_comm]
      rw [← add_assoc]
      suffices i2 : 0 ≤ 2 + 2 * s + 100 * |s|
      positivity
      rw [show (100:ℝ) = 2 * 50 by norm_num, mul_assoc, add_assoc, ← mul_add]
      nth_rw 1 [← mul_one 2]
      rw [← mul_add]
      simp
      rw [← neg_le_iff_add_nonneg']
      trans 0
      norm_num
      rw [←neg_le_iff_add_nonneg']
      trans |s|
      apply neg_le_abs
      have i0 : 0 ≤ |s| := by positivity
      linarith
      rw [add_le_add_iff_right]
      assumption
      assumption
      rw [add_comm, ← neg_le_iff_add_nonneg',← neg_mul, neg_mul_comm]
      trans 2 * |s|
      field_simp
      apply neg_le_abs
      assumption
    have fs_nn := f_nonneg √(x + 2 * s) i2
    have fr_nn := f_nonneg √(x + 2 * r) i1
    rw [mul_comm] at fs_nn fr_nn
    rw [sq_eq_sq₀ fs_nn fr_nn] at hr
    symm at hr
    assumption
    rw [← neg_le_iff_add_nonneg, ← neg_mul]
    trans 2 * |s|
    field_simp
    apply neg_le_abs
    assumption
    rw [← neg_le_iff_add_nonneg, ← neg_mul]
    trans 2 * |r|
    field_simp
    apply neg_le_abs
    assumption


  have ⟨M₁, m1pos, m1r, m1s, heq⟩ := fsq_eq
  have hsqsub : 0 < (√(M₁ + 2*r) - √(M₁ + 2*s)) := by
    rw [sub_pos, sqrt_lt_sqrt_iff]
    linarith
    apply neg_le_iff_add_nonneg.mp
    trans 2 * |s|
    field_simp
    apply neg_le_abs
    linarith
  have ⟨ε, epos, hε⟩ := exists_between hsqsub
  have ⟨a, ha⟩ := exists_between (by linarith: ε/2 < ε)
  have ⟨u, v, huv⟩ : ∃u v:ℝ, u^2 - v^2 = a := by
    use (sqrt (a)), 0
    rw [sq_sqrt]
    simp
    linarith

  have apos : 0 < a := by linarith
  obtain ⟨elb, eub⟩ := ha
  have har: 0 ≤ ((r - s) ^ 2 / a ^ 2 + a ^ 2 / 4 - r - s + 2 * r) := by
    rw [add_sub_assoc, add_sub_assoc,add_assoc]
    rw [show a ^ 2 / 4 - r - s + 2*r = a ^ 2 / 4 + r - s by ring_nf, ← add_sub_assoc, ← add_assoc, add_sub_assoc]
    positivity

  have has: 0 ≤ ((r - s) ^ 2 / a ^ 2 + a ^ 2 / 4 - r - s + 2 * s) := by
    rw [add_sub_assoc, add_sub_assoc,add_assoc]
    rw [show a ^ 2 / 4 - r - s + 2*s = a ^ 2 / 4 + s - r by ring_nf, ← add_sub_assoc, ← add_assoc, add_sub_assoc, sub_sq_comm]
    field_simp
    simp
    generalize (s-r) = n
    rw [show n ^ 2 * 4 + a ^ 4 + n * a ^ 2 * 4 = (2*n+a^2)^2 by ring_nf]
    apply sq_nonneg

  have hi : 0 <  M₁ + 2*r := by grind
  have hj : 0 <  M₁ + 2*s := by grind
  have ⟨b, hb⟩ : ∃B:ℝ, sqrt (B+2*r) - sqrt (B+2*s) = a := by
    use ((r - s)^2/a^2 + a^2/4 - r - s)
    apply sub_eq_of_eq_add
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]
    rw [add_sq', sq_sqrt, sq_sqrt]
    let w' := √((r - s) ^ 2 / a ^ 2 + a ^ 2 / 4 - r - s + 2 * s)
    have hw' : 0 ≤ w' := by
      unfold w'
      positivity
    change (r - s) ^ 2 / a ^ 2 + a ^ 2 / 4 - r - s + 2 * r = a ^ 2 + ((r - s) ^ 2 / a ^ 2 + a ^ 2 / 4 - r - s + 2 * s) + 2 * a * w'
    rw [← add_assoc, ← add_sub_assoc, ← add_sub_assoc, ← add_assoc,add_comm (a^2)]
    let n' := a ^ 2 / 4 - (r + s)
    rw [show (r - s) ^ 2 / a ^ 2 + a ^ 2 / 4 - r - s + 2 * r = (r - s) ^ 2 / a ^ 2 + (n' + 2 * r) by ring]
    rw [show (r - s) ^ 2 / a ^ 2 + a ^ 2 + a ^ 2 / 4 - r - s + 2 * s + 2 * a * w' = (r - s) ^ 2 / a ^ 2 + (n'
   +( a ^ 2 + 2 * s + 2 * a * w')) by ring]
    rw [add_left_cancel_iff, add_left_cancel_iff, add_assoc]
    apply eq_add_of_sub_eq'
    apply eq_add_of_sub_eq'
    rw [sub_sub, add_comm, ← sub_sub, ← mul_sub]
    rw [show a^2 = 2*(a^2 /2) by ring, ← mul_sub, mul_assoc, mul_left_cancel_iff_of_pos (by positivity: (0:ℝ) < 2), mul_comm]
    rw [← div_left_inj' (by linarith: a ≠ 0), mul_div_assoc, div_self, mul_one]
    rw [← sq_eq_sq₀]
    unfold w'
    rw [sq_sqrt]
    ring_nf
    field_simp
    ring_nf
    exact has
    field_simp
    simp

    have i0 : √(M₁ + 2 * r) - √(M₁ + 2 * s) ≤ (M₁ + 2 * r) - (M₁ + 2 * s) := by

      have hk : M₁ + 2*s < M₁ + 2*r := by linarith
      have hg1 : 1 < sqrt (M₁ + 2*r) + sqrt (M₁ + 2*s) := by
        have hg3: 0 ≤ sqrt (M₁ + 2*s) := by apply sqrt_nonneg
        suffices hg2: 1 < sqrt (M₁ + 2*r)
        linarith
        rw [← sqrt_one, sqrt_lt_sqrt_iff]
        trans 2 * |r| + 2 + 2 * r
        rw [add_rotate]
        suffices hg4: 0 ≤ 2 * r + 2 * |r|
        linarith
        rw [← mul_add]
        simp
        rw [← neg_le_iff_add_nonneg']
        apply neg_le_abs
        rw [add_lt_add_iff_right]
        assumption
        norm_num




      generalize M₁ + 2*r = i at hi hk hg1
      generalize M₁ + 2*s = j at hj hk hg1
      have root1 : i - j = (sqrt i)^2 - (sqrt j)^2 := by
        rw [sq_sqrt (le_of_lt hi), sq_sqrt (le_of_lt hj)]

      rw [root1, sq_sub_sq]
      have eq1: 0 ≤ (√i - √j) := by
        simp
        apply sqrt_le_sqrt
        exact le_of_lt hk
      generalize √i - √j = k at eq1
      apply le_mul_of_one_le_left
      assumption
      exact le_of_lt hg1
    rw [← sqrt_le_sqrt_iff, sqrt_sq (le_of_lt apos)]
    trans √(M₁ + 2 * r) - √(M₁ + 2 * s)
    linarith
    rw [← sq_le_sq₀, sq_sqrt]
    ring_nf
    rw [sq_sqrt, sq_sqrt]
    ring_nf
    rw [← add_mul, ← sub_mul, ← add_mul, ← sub_mul]
    simp
    rw [← sqrt_mul]
    trans M₁ + r - √((M₁ + s * 2) * (M₁ + s * 2)) + s
    simp
    rw [add_sub_assoc, add_assoc]
    apply add_le_add_right
    rw [sub_add_comm]
    nth_rw 1 [← zero_add r]
    apply add_le_add_left
    rw [sub_nonneg]
    apply sqrt_le_sqrt
    rw [mul_le_mul_iff_of_pos_right]
    linarith
    grind
    rw [sqrt_mul_self]
    linarith
    any_goals positivity
    all_goals linarith
  h
















snip end
theorem imo2004SLA6(f: ℝ→ℝ): f ∈ solution_set ↔ ∀x y, f (x^2 + y^2 + 2*f (x*y)) = (f (x+y))^2:= by

  constructor
  · simp
    intro h x y
    rcases h with e | e | help
    · simp [e]
      ring_nf
    · simp [e]
    obtain ⟨X, hX, hf⟩ := help
    have i1 : 4*(x*y) ≤ (x+y)^2 := by
      rw [← mul_assoc]
      exact four_mul_le_sq_add x y

    have e1 : (x+y)^2 - 2*(x*y) = x^2 + y ^2 := by ring_nf
    generalize x + y = a at i1 e1
    generalize x * y = b at i1 e1
    rw [← e1, sub_add_eq_add_sub]
    have hf2 : ∀w, (f w)^2 = 1 := by
      intro w
      by_cases hw: w < X
      · have fw := hf w
        simp [hw] at fw
        rw [fw]
        simp
      have fw := hf w
      simp [hw] at fw
      rw [fw]
      simp
    by_cases hb : b < 0
    · rw [hf2]
      suffices hs1 : ¬ X > a^2 + 2*f b - 2*b
      · have hf0 := hf (a^2 + 2*f b - 2*b)
        simp [hs1] at hf0
        assumption
      simp
      trans -2/3
      · linarith
      trans 2 * f b - 2 * b
      · by_cases hbx: b < X
        · have fb := hf b
          simp [hbx] at fb
          rw [fb]
          norm_num
          linarith
        have fb := hf b
        simp [hbx] at fb
        rw [fb]
        norm_num
        linarith
      rw [sub_le_sub_iff_right]
      simp [sq_nonneg]
    have fb := hf b
    have hbx : ¬ b < X := by linarith
    simp [hbx] at fb
    rw [fb, hf2]
    norm_num
    suffices hs: ¬ a ^ 2 + 2 - 2 * b < X
    · have fb2 := hf (a ^ 2 + 2 - 2 * b)
      simp [hs] at fb2
      assumption
    push Not
    trans 0
    · linarith
    have i2 : 2 + 2*b ≤ a^2 + 2 - 2*b := by linarith
    suffices hs: 0 ≤2 + 2*b
    · linarith
    linarith
  intro h
  by_cases hi: Injective f
  · have fid:= inj_id f h hi
    simp
    left
    assumption
  rw [Function.not_injective_iff] at hi
  obtain ⟨a, b, hfab, habne⟩ := hi
  wlog hab: a < b generalizing a b
  · push Not at hab
    apply lt_or_eq_of_le at hab
    simp [habne.symm] at hab
    specialize this b a hfab.symm habne.symm hab
    assumption
  have ⟨k, kpos, hk⟩ : ∃k>0, b = a+k := by
    use b-a
    simp
    assumption
  rw [hk] at hfab





  sorry

end imo2004a6
