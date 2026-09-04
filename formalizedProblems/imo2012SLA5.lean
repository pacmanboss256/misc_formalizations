/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic

public import ProblemExtraction
public import Mathlib.Algebra.Order.Archimedean.Real.Hom

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 2012 A5
Find all functions f: ℝ → ℝ such that
f(1+xy) - f(x+y) = f(x)f(y) and f (-1) ≠ 0
-/

namespace imo2012A5
determine solution_set: Set (ℝ→ℝ):= {fun x ↦ x-1}
open Real
snip begin
variable (f:ℝ→ℝ)(h:∀x y:ℝ, f (1+x*y) - f (x+y) = f x * f y)(fne: f (-1) ≠ 0)
include f h fne
lemma f1: f 1 = 0 := by
  have f1:= h 1 (-1)
  simp [fne] at f1
  assumption

lemma f0: f 0 = -1 := by
  have f0 := h (-1) 0
  simp [f1 f h fne] at f0
  rw [mul_comm, ← div_eq_iff fne, neg_div_self fne] at f0
  symm at f0
  assumption


lemma l1: ∀x, f (1-x) + f (1+x) = 0 := by
  intro x
  have h1 := h (-1) (1-x)
  have h2 := h (-1) (1+x)
  ring_nf at h1 h2
  have h3: f x - f (-x) + - f x + f (-x) = f (-1)*f (1-x) + f (-1) * f (1+x) := by rw [h1, add_assoc, h2]
  ring_nf at h3
  symm at h3
  rwa [← mul_add, mul_eq_zero_iff_left fne] at h3

lemma l2: ∀x, f x = - f (2-x) := by
  intro x
  have h1 := h x (-1)
  specialize h (2-x) (-1)
  ring_nf at h h1
  have h3: f (-1 + x) - f (1 - x) + -f (-1 + x) + f (1 - x) = f (2 - x) * f (-1) + f (-1) * f x := by
    rw [← h, ← h1]
    ring
  ring_nf at h3
  symm at h3
  rw [mul_comm, ←mul_add, mul_eq_zero_iff_left fne, add_eq_zero_iff_eq_neg'] at h3
  assumption


lemma l2': ∀x, f (2+x) = - f (-x) := by
  intro x
  have h1 := l2 f h fne (-x)
  simp at h1
  rw [← neg_eq_iff_eq_neg] at h1
  symm
  assumption

lemma l3: ∀a b:ℝ, b ≤ 0 → f (2+a) - f (2-a) = f (2 + a + b) - f (2 - a + b):= by
  intro a b hab
  have ⟨x, y, ha, hb⟩: ∃x y:ℝ, x+y = a ∧ x*y = b := by
    use ((a + sqrt (a^2 - 4*b))/2), ((a - sqrt (a^2 - 4*b))/2)
    ring_nf
    rw [sq_sqrt]
    · ring_nf; simp
    rw [sub_nonneg]
    trans 0
    · linarith
    exact sq_nonneg a
  have h1 := h (1-x) (1-y)
  have h2 := h (1+x) (1+y)
  ring_nf at h1 h2
  rw [show 2 - x + x*y - y = 2 - (x + y) + x*y by ring, sub_sub] at h1
  rw [show 2 + x + x*y + y = 2 + (x + y) + x*y by ring, add_assoc 2 x y] at h2
  have hnx := l2 f h fne (1+x)
  have hny := l2 f h fne (1+y)
  ring_nf at hnx hny
  rw [ha, hb] at h1 h2
  rw [hnx, hny] at h2
  ring_nf at h2
  rw [← h1, sub_eq_sub_iff_sub_eq_sub] at h2
  symm
  assumption

lemma l4: ∀a k,f a - f (-a) =f (a+k)-f (-a+k) := by
  intro a k
  by_cases! hk: k ≤ 0
  · have hk': k - 2 ≤ 0 := by linarith
    have h1 := l3 f h fne a (k-2) hk'
    ring_nf at h1
    rw [l2 f h fne (2-a), l2 f h fne (2+a)] at h1
    ring_nf at h1
    rwa [neg_add_eq_sub] at h1
  apply le_of_lt at hk
  have hk': -k ≤ 0 := by linarith
  have h1 := l3 f h fne a (-k) hk'
  ring_nf at h1
  have l2 := l2 f h fne
  rw [show 2 - a - k = 2 + (-a - k) by ring] at h1
  rw [l2 (2-a), l2 (2+a), l2 (2+a-k), l2 (2 + (-a-k))] at h1
  ring_nf at h1
  rwa [neg_add_eq_sub, neg_add_eq_sub] at h1


lemma f2: f 2 = 1 := by
  have f2 := l2 f h fne 0
  simp [f0 f h fne] at f2
  symm
  assumption


lemma e1: ∀x, f x + f (x+2) + f (-1) * f (x + 1) = 0 := by
  intro x
  have h0 := h x (-1)
  have h1 := h (x+1) (-1)
  have h2 := h (x+2) (-1)
  ring_nf at h0 h1 h2
  rw [← eq_sub_iff_add_eq'] at h1
  rw [← eq_sub_iff_add_eq'] at h2
  have h3 := h (-x) (-1)
  ring_nf at h3
  rw [sub_eq_iff_eq_add, mul_comm, add_comm _ (f (-1 -x)), h2,h1] at h3
  ring_nf at h3
  rw [right_eq_add, ← mul_add, pow_two, mul_assoc, ← mul_add, mul_eq_zero_iff_left fne] at h3
  ring_nf
  rw [add_comm (f x)]
  assumption

lemma fn1: f (-1) = -2 := by
  let c := f (-1)
  have e1 := e1 f h fne
  have f0 := f0 f h fne
  have f1 := f1 f h fne
  have f2 := f2 f h fne
  have f3:= e1 1
  ring_nf at f3
  simp [f1, f2] at f3
  rw [add_eq_zero_iff_eq_neg] at f3
  have f4 := e1 2
  norm_num at f4
  simp [f2, f3] at f4
  ring_nf at f4
  rw [add_comm, sub_eq_zero, ← eq_sub_iff_add_eq] at f4
  have f5 := e1 3
  ring_nf at f5
  simp [f3, f4] at f5
  ring_nf at f5
  rw [add_eq_zero_iff_eq_neg, ← neg_eq_iff_eq_neg] at f5
  symm at f5
  ring_nf at f5
  have f5' := h 2 2
  ring_nf at f5'
  simp [f2] at f5'
  rw [sub_eq_iff_eq_add, f4] at f5'
  ring_nf at f5'
  rw [f5', pow_two, pow_three, ← mul_sub, mul_right_inj' fne,← sub_eq_zero] at f5
  rw [show c - (2-c*c) = (c-1) * (c+2) by ring_nf, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at f5
  rcases f5 with one | two
  have t: ∀x, f (x) = f (3 + x) := by
    intro z
    have ⟨x, hx⟩: ∃x, x = -z - 1 := by use -z-1
    have h1 := h (x+1) (-1)
    have h2 := h (x+2) (-1)
    ring_nf at h1 h2
    simp [show f (-1) = c by rfl, one] at h1 h2
    rw [l2' f h fne, neg_add_eq_sub, ← h1] at h2
    ring_nf at h2
    rw [sub_add_eq_add_sub, eq_neg_iff_add_eq_zero] at h2
    simp at h2
    rw [l2 f h fne x, add_neg_eq_zero] at h2
    rw [hx] at h2
    ring_nf at h2
    assumption
  have ht: ∀x, f (3*x+1) = 0 := by
    intro x
    have h1 := h x 3
    ring_nf at h1
    rw [← t] at h1
    simp [f3] at h1
    rw [show f (-1) = c by rfl] at h1
    simp [one] at h1
    ring_nf
    assumption
  specialize ht (-2/3)
  ring_nf at ht
  tauto
  unfold c at two
  assumption

lemma f3: f 3 = 2 := by
  have h1 := l1 f h fne 2
  ring_nf at h1
  rw [fn1 f h fne] at h1
  rw [add_eq_zero_iff_eq_neg'] at h1
  simp at h1
  assumption

lemma lin: ∀x, f x + f (-x) = -2 := by
  intro x
  have h1 := l4 f h fne 1 (1-x)
  simp [f1 f h fne, fn1 f h fne] at h1
  ring_nf at h1
  rw [eq_sub_iff_add_eq, ← sub_eq_zero, sub_eq_add_neg, ← l2 f h fne x, add_assoc, add_comm, add_eq_zero_iff_eq_neg, add_comm] at h1
  assumption


theorem linear_add: ∀x y, f (x+y) + f (x-y) = 2*f x := by
  intro x y
  have h1:= h x y
  have h2:= h x (-y)
  ring_nf at h2
  have h3: f (1 + x * y) - f (x + y) +  f (1 - x * y) - f (x - y) = f x * (f y + f (-y)) := by
    rw [h1, add_sub_assoc, h2]
    ring
  rw [← add_sub_right_comm, add_comm, l1 f h fne (x*y),lin f h fne y, mul_comm] at h3
  simp at h3
  rw [← neg_eq_iff_eq_neg] at h3
  simp at h3
  rwa [add_comm] at h3

lemma offset_add: ∀x, f x = f (x+1) - 1 := by
  intro x
  have h1 := h (x+1) (-1)
  ring_nf at h1
  apply_fun (fun x ↦ x - -2) at h1
  nth_rw 1 [← lin f h fne x, fn1 f h fne] at h1
  ring_nf at h1
  field_simp at h1
  rw [neg_eq_iff_eq_neg] at h1
  ring_nf at h1
  rwa [add_comm, ← sub_eq_add_neg, add_comm] at h1

lemma additive: ∀x y:ℝ, f (x+y) = f x + f y + 1 := by
  have hadd := offset_add f h fne
  intro x y
  by_cases! hy: y = 0
  rw [hy]
  simp [f0 f h fne]
  have ⟨i, hi⟩: ∃i, x = 1+i*y := by
    use (x-1)/y
    rw [div_mul, div_self]
    simp
    assumption
  have hx := h i y
  have hx1 := h (i+1) y
  ring_nf at hx hx1
  have h3 : f (1 + i * y + y) - f (1 + i + y) - (f (1 + i * y) - f (i + y)) = f y * f (1 + i) - f i * f y := by
    rw [← hx, ← hx1]
  rw [hadd (i+y)] at h3
  ring_nf at h3
  rw [hadd i] at h3
  ring_nf at h3
  rw [← hi] at h3
  rw [sub_eq_iff_eq_add, ← eq_sub_iff_add_eq', add_comm (f y)] at h3
  simp at h3
  assumption

lemma multiplicative: ∀x y, f (x*y) + 1 = (f x + 1) * (f y + 1):= by
  intro x y
  have hadd := additive f h fne
  have h1 := h x y
  ring_nf at h1
  simp [hadd, f1 f h fne] at h1
  ring_nf at h1
  rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at h1
  apply_fun (· + 1) at h1
  rw [show f x * f y + f y + f x + 1 = (f x + 1) * (f y + 1) by ring_nf] at h1
  assumption

theorem shift: ∀x, f x = x - 1 := by
  let g := fun w ↦ f w + 1
  have hadd := additive f h fne
  have gadd: ∀x y, g (x+y) = g x + g y := by
    intro x y
    unfold g
    simp [hadd]
    ring_nf
  have hmul: ∀x y, g (x*y) = g x * g y := by
    intro x y
    unfold g
    exact multiplicative f h fne x y

  have hg: ∀x y, g (x*y) - g (x+y) + 1 = (g x - 1) * (g y - 1) := by
    intro x y
    have h1 := h x y
    simp [hmul, gadd]
    unfold g
    ring_nf

  have g0: g 0 = 0 := by
    unfold g
    simp [f0 f h fne]

  have g1: g 1 = 1 := by
    unfold g
    simp [f1 f h fne]

  let gring : ℝ →+* ℝ := {
    toFun := g
    map_zero' := g0
    map_one' := g1
    map_add' := gadd
    map_mul' := hmul
  }
  have ge: gring = RingHom.id ℝ := by
    ext x'
    simp

  have g2: ∀x, g x = x := by
    intro x
    have geq: gring.toFun = (RingHom.id ℝ).toFun := by simp [ge]
    simp at geq
    change g = id at geq
    apply congr_fun at geq
    specialize geq x
    simp at geq
    assumption

  unfold g at g2
  intro x
  specialize g2 x
  rw [← eq_sub_iff_add_eq] at g2
  assumption





snip end

omit f h fne in
theorem imo2012SLA5(f:ℝ→ℝ)(fne: f (-1) ≠ 0):
  f ∈ solution_set ↔ ∀x y:ℝ, f (1+x*y) - f (x+y) = f x * f y := by
  constructor
  intro h x y
  simp at h
  simp [h]
  ring_nf
  intro h
  have ans:= shift f h fne
  simp
  funext w
  specialize ans w
  assumption




end imo2012A5
