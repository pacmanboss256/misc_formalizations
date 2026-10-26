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
## Putnam 1953 A3
show 2(a+b+c)(a^2+b^2+c^2)/3 > a^3+b^3+c^3+abc

for a b c such that the sum of any two is greater than the third
-/

namespace putnam1953

lemma subst(a b c: ℝ)(htr1: a + b > c)(htr2: a + c > b)(htr3: b + c > a):
  ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c - a) / 2, (a + c - b) / 2, (a + b - c) / 2
  refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
  linarith; linarith; linarith


problem putnam1953A3(a b c:ℝ)(htr1: a + b > c)(htr2: a + c > b)(htr3: b + c > a): a^3+b^3+c^3+a*b*c < 2*(a+b+c)*(a^2+b^2+c^2)/3  := by
  wlog! hab: a ≤ b generalizing a b c
  rw [add_comm] at htr1
  specialize this b a c htr1 htr3 htr2 (le_of_lt hab)
  linarith
  wlog! hac: a ≤ c generalizing a c
  rw [add_comm] at htr3 htr2 htr1
  specialize this c a htr3 htr2 htr1 (by linarith) (le_of_lt hac)
  linarith
  wlog! hbc: b ≤ c generalizing b c
  rw [add_comm] at htr3
  specialize this c b htr2 htr1 htr3 hac hab (le_of_lt hbc)
  linarith
  field_simp
  have ⟨x,y,z, xpos, ypos,zpos, ha, hb, hc⟩:= subst a b c htr1 htr2 htr3
  have hyx: y ≤ x := by linarith
  have hzy: z ≤ y := by linarith
  rw [← sub_pos, ha, hb,hc]
  ring_nf
  positivity

end putnam1953
