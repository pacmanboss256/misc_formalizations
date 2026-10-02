/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
## IMC 2024 day 1 problem 1
Determine all pairs (a,b) ∈ ℂ² where |a|=|b|=1 and a+b+a b* ∈ ℝ
-/
namespace imc2024

determine solution_set: Set (ℂ × ℂ):= {(a,b)| (a = 1 ∧ ‖b‖ = 1) ∨(‖a‖ = 1 ∧ b = -1) ∨ (‖a‖ = 1 ∧ ‖b‖ = 1 ∧ b = -a)}

problem imc2024d1p1: ∀a b, (((a,b) ∈ solution_set ↔ (‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a+b+a* star b).im = 0))):= by
  intro a b
  constructor
  intro abs
  unfold solution_set at abs
  simp at abs
  rcases abs with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  <;> simp [ha, hb]
  ring_nf
  intro ⟨ha, hb, hr⟩
  




end imc2024
