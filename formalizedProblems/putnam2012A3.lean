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
## Putnam 2012 A3
let f: [-1, 1] → ℝ be continuous where

a) f x = (2-x^2)/2 * f (x^2 / (2-x^2))

b) f 0 = 1

c) lim x -> 1⁻ of f x exists

show f is unique and express it in closed form
-/

namespace putnam

def S: Set ℝ := Set.Icc (-1) 1

def conditions(f:ℝ→ℝ): (∀x ∈ S, f x = (2-x^2)/2 * f (x^2/(2-x^2))) ∧ f 0 = 1 ∧ 


end putnam
