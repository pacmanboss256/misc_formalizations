/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic

public import ProblemExtraction

public import Mathlib.Data.PNat.Basic


@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMO Shortlist 2010 A6
Suppose that $f$ and $g$ are two functions defined on the set of positive integers and taking positive integer values. Suppose also that the equations $f(g(n)) = f(n) + 1$ and $g(f(n)) = g(n) + 1$ hold for all positive integers. Prove that $f(n) = g(n)$ for all positive integer $n.$

-/

namespace IMO2010A6
open PNat Set

theorem imo2010SLA6(f g: ℕ+ → ℕ+)(feq: ∀n, f (g n) = f n + 1)(geq: ∀n, g (f n) = g n + 1): ∀n, f n = g n := by
  have eq_iff: ∀n m, f n = f m ↔ g n = g m := by
    intro n m
    constructor
    intro hf
    apply_fun g at hf
    simp [geq] at hf
    assumption
    intro hg
    apply_fun f at hg
    simp [feq] at hg
    assumption

  have ⟨fiter, giter⟩: (∀n m, (f (f m) = f (f n) → f m = f n)) ∧ ∀n m, (g (g m) = g (g n) → g m = g n) := by
    constructor
    intro n m hfiter
    simp [eq_iff, geq] at hfiter
    rwa [← eq_iff m n] at hfiter
    intro n m hgiter
    simp [← eq_iff, feq] at hgiter
    rwa [eq_iff m n] at hgiter

  have ⟨fne, gne⟩: (∀n, f n ≠ n) ∧ ∀n, g n ≠ n := by
    constructor
    intro n
    by_contra! hn
    specialize geq n
    rw [hn, add_comm] at geq
    have i1:= PNat.lt_add_left (g n) 1
    rw [← geq] at i1
    simp at i1
    intro n
    by_contra! hn
    specialize feq n
    rw [hn, add_comm] at feq
    have i1:= PNat.lt_add_left (f n) 1
    rw [← feq] at i1
    simp at i1











end IMO2010A6
