/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Order.Interval.Set.Nat
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## Putnam 1963 A2
Let f: ℕ→ℕ be a strictly increasing function such that $f(2)=2$ and $f(mn)=f(m)f(n)$
for every pair of relatively prime positive integers $m$ and $n$. Prove that $f(n)=n$ for every positive integer $n$.
-/

namespace putnam1963

lemma f3(f:ℕ→ℕ)(hm: StrictMono f)(f2: f 2 = 2)
  (hf: ∀n m, n.Coprime m → f (m*n) = f m * f n)
  (fodd: ∀n, Odd n → f (2*n) = 2*f n)(f1: f 1 = 1): f 3 = 3:= by
    let k := f 3
    have k3: 3 ≤ k := by
      by_contra!
      have hc: f 2 < k := by apply hm; decide
      rw [f2] at hc
      lia
    have f6:= fodd 3 (by decide)
    change f 6 = 2*k at f6
    have f5a: f 5 ≤ 2*k-1 := by
      rw [← f6, Nat.le_sub_iff_add_le]
      apply Nat.add_one_le_of_lt
      apply hm; decide
      rw [← f1]
      apply le_of_lt
      apply hm; decide
    have f5b: k+2 ≤ f 5 := by
      change f 3 + 2 ≤ f (3+2)
      rw [add_comm]
      apply StrictMono.add_le_nat hm
    have f15: f 15 ≤ 8*k - 9 := by
      have f10: f 10 ≤ 4*k - 2 := by
        have e1:= fodd 5 (by decide)
        simp at e1
        rw [e1]
        lia
      have f9: f 9 ≤ 4*k - 3 := by
        have e1: 4 * k + 1 - 3 = 4*k - 2 := by lia
        rw [Nat.le_iff_lt_add_one, ← Nat.sub_add_comm (by lia), e1]
        suffices: f 9 < f 10
        lia; apply hm; decide
      have f18: f 18 ≤ 8*k - 6 := by
        have e1:= fodd 9 (by decide)
        simp at e1
        rw [e1]
        lia
      have f17: f 17 ≤ 8*k - 7 := by
        suffices: f 17 < f 18
        lia; apply hm; decide
      have f16: f 16 ≤ 8*k - 8 := by
        suffices: f 16 < f 17
        lia; apply hm; decide
      suffices: f 15 < f 16
      lia; apply hm; decide
    have h15:= hf 5 3 (by decide)
    simp at h15
    have i1: k*(k+2) ≤ 8*k - 9 := by
      trans (f 15)
      rw [h15]
      apply mul_le_mul'; lia; lia
      assumption
    ring_nf at i1
    zify at i1
    have i2: 9 ≤ k*8 := by lia
    rw [Int.natCast_sub i2] at i1
    push_cast at i1
    nth_rw 3 [← neg_neg (k:ℤ)] at i1
    rw [show - -(k:ℤ) * 8 - 9 = -(9-k*8) by simp, ← Int.add_le_zero_iff_le_neg] at i1
    ring_nf at i1
    rw [show 9 - ↑k * 6 + ↑k ^ 2 = ((k:ℤ)-3)^2 by ring_nf] at i1
    simp at i1
    lia

problem putnam1963A2(f:ℕ→ℕ)(hm: StrictMono f)(f2: f 2 = 2)
  (hf: ∀n m, n.Coprime m → f (m*n) = f m * f n): ∀n, f n = n:= by
  have f1: f 1 = 1 := by
    specialize hf 2 1 (by decide)
    rw [one_mul, f2] at hf
    simp at hf
    assumption

  have f0: f 0 = 0 := by
    have h0: f 0 < f 1 := by apply hm; decide
    rw [f1] at h0
    lia

  have fodd: ∀n, Odd n → f (2*n) = 2*f n := by
    intro n hn
    specialize hf n 2 (by exact Odd.coprime_two_right hn)
    rwa [f2] at hf

  have f3:= f3 f hm f2 hf fodd f1
  have f6: f 6 = 6 := by
    specialize hf 3 2 (by decide)
    simp [f2, f3] at hf
    assumption
  have f5: f 5 = 5 := by
    have i1: 5 ≤ f 5 := by apply StrictMono.id_le hm
    have i2: f 5 < f 6 := by apply hm; decide
    lia
  have f4: f 4 = 4 := by
    have i1: 4 ≤ f 4 := by apply StrictMono.id_le hm
    have i2: f 4 < f 5 := by apply hm; decide
    lia
  have hpow: ∀s, f (2^s + 1) = 2^s+1:= by
      intro t
      induction t with
      | zero => simp; assumption
      | succ t ih' =>
        by_cases! hs: t ≤ 0
        simp at hs
        simp [hs]; assumption
        rw [pow_succ]
        suffices: Odd (2^t+1)
        specialize fodd (2^t+1) this
        rw [ih'] at fodd
        ring_nf at fodd
        have i1: 2 ^ t * 2 + 1 ≤ f (2 ^ t * 2 + 1):=  by apply StrictMono.id_le hm
        have i2:f (1+2 ^ t * 2)< f (2 + 2 ^ t * 2) := by apply hm; lia
        lia
        rw [Nat.odd_add']
        simp
        rw [Nat.even_pow]
        exact ⟨by decide, by positivity⟩

  intro n
  induction n using Nat.case_strong_induction_on with
  | hz => assumption
  | hi n ih =>
    have hle: ∀x, x ≤ f x := by intro x; apply StrictMono.id_le hm
    by_contra! hne
    apply lt_or_gt_of_ne at hne
    rcases hne with lt | gt
    specialize hle (n+1); linarith
    have h1:f '' Set.Ioc (n+1) (2^n+1) ⊆ Set.Ioc (f (n+1)) (f (2^n+1)):= by
      apply StrictMono.image_Ioc_subset hm

    rw [hpow n] at h1
    apply Set.card_le_card at h1
    simp at h1
    have h2:= Nat.card_image_of_injective (by apply StrictMono.injective hm) (Set.Ioc (n+1) (2^n+1))
    simp at h2
    rw [h2, Nat.sub_le_iff_le_add] at h1
    apply_fun (· + f (n+1)) at h1
    norm_num1 at h1
    rw [add_assoc, add_comm n (f (n+1)), ← add_assoc, Nat.sub_add_cancel, add_assoc, Nat.add_le_add_iff_left] at h1
    lia
    rw [← hpow n]
    apply le_of_lt
    apply hm
    rw [Nat.add_lt_add_iff_right]
    apply Nat.lt_two_pow_self
    apply Monotone.add_const
    apply monotone_id


end putnam1963
