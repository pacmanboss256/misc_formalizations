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
## IMC 2024 day 2 problem 1
Prove that for any function f : Q → Z, there exist a, b, c ∈ Q such that a < b < c,
f (b) ≥ f (a), and f (b) ≥ f (c)
-/
namespace imc2024
open Function

problem imc2024d2p6: ∀f:ℚ→ℤ, (∃a b c:ℚ, (a < b ∧ b < c) ∧ f b ≥ f a ∧ f b ≥ f c):= by
  intro f
  wlog! hf01: f 0 ≤ f 1
  specialize this (fun w ↦ f (1-w))
  simp at this
  specialize this (le_of_lt hf01)
  obtain ⟨a, b, c, hab, hf⟩ := this
  simp
  use 1-c, 1-b, 1-a
  simp [hab, hf]
  by_cases! hf12: f 2 ≤ f 1
  use 0,1,2
  simp [hf01, hf12]
  by_cases hx: ∃x, 1 < x ∧ x < 2 ∧ f 2 ≤ f x
  obtain ⟨x, hx12, hfx⟩ := hx
  use 1,x,2
  constructor
  lia; lia
  by_cases hx': ∃x, 1 < x ∧ x < 2 ∧ f x ≤ f 1
  obtain ⟨x, hx12, hfx⟩ := hx'
  use 0,1,x
  constructor; simp; lia; lia
  simp at hx hx'
  have hf: ∀x, (x ∈ Set.Ioo 1 2 → f x ∈ Finset.Ioo (f 1) (f 2)) := by
    intro x
    simp
    intro h1 h2
    specialize hx x h1 h2
    specialize hx' x h1 h2
    lia

  have hmap: Set.MapsTo f (Set.Ioo (1:ℚ) 2) (Finset.Ioo (f 1) (f 2)) := by
    unfold Set.MapsTo
    apply hf

  have sinf: (Set.Ioo (1:ℚ) 2).Infinite := by
    apply Set.Ioo_infinite; decide

  have h1:= Set.Infinite.exists_lt_map_eq_of_mapsTo sinf hmap (by simp)
  obtain ⟨x, hxi, y, hyi, ⟨xylt, hfeq⟩⟩:= h1
  have hmap2: Set.MapsTo f (Set.Ioo (x:ℚ) y) (Finset.Ioo (f 1) (f 2)) := by
    unfold Set.MapsTo
    intro q hq
    suffices: q ∈ (Set.Ioo (1:ℚ) 2)
    apply hf at this
    assumption
    simp
    simp at hq hyi hxi
    constructor
    trans x
    lia; lia
    trans y
    lia; lia

  have sinf2: (Set.Ioo x y).Infinite := by
    apply Set.Ioo_infinite
    simp at hyi
    lia

  have h1:= Set.Infinite.exists_lt_map_eq_of_mapsTo sinf2 hmap2 (by simp)
  obtain ⟨x', hxi', y', hyi', ⟨xylt', hfeq'⟩⟩ := h1
  have order: x < x' ∧ x' < y' ∧ y' < y := by
    simp at hxi hyi hxi' hyi'
    lia

  rcases (lt_trichotomy (f x) (f x')) with lt | eq | gt
  use x, x', y
  rw [← hfeq]
  simp [order, (le_of_lt lt)]
  simp at hxi'; lia
  use x, x', y
  rw [← hfeq]
  simp [order, eq]
  simp at hxi'; lia
  use 1, x, x'
  simp at hxi
  simp [order, hxi, (le_of_lt gt)]
  exact (le_of_lt ((hx' x hxi.left hxi.right)))























end imc2024
