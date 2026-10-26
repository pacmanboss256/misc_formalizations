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
## IMC 2001 D2 P5
show there is no function
f(x+y) ≥ f(x) +yf(f(x)) with 0 < f 0 for all x y in ℝ
-/

namespace imc2001
open Filter Function
problem imc2001P5: ¬∃f:ℝ→ℝ, (0 < f 0 ∧ ∀x y, f x + y * f (f x) ≤ f (x+y)):= by
  by_contra hf
  obtain ⟨f, f0, hf⟩:= hf
  have ⟨z, hz⟩: ∃z, 0 < f (f z) := by
    by_contra hz
    simp at hz
    have h1: ∀x, ∀y ≤ 0, f x ≤ f (x+y) := by
      intro x y hy
      specialize hf x y
      apply LE.le.trans' hf
      specialize hz x
      rw [le_add_iff_nonneg_right, mul_nonneg_iff]
      right; exact ⟨hy, hz⟩
    have i1:= hz 0
    specialize h1 0 (f (f 0)) i1
    simp at h1
    specialize hz (f 0)
    linarith

  have h1: ∀x ≥ 0, 0 ≤ f (z+x)-f z := by
    intro x hx
    have hf':= hf z x
    rw [← le_sub_iff_add_le'] at hf'
    apply LE.le.trans' hf'
    positivity

  let g: ℝ→ℝ:= fun w ↦ f z + (w-z)* f (f z)
  have glim: Tendsto g atTop atTop := by
    unfold g
    apply tendsto_atTop_add_const_left
    apply Tendsto.atTop_mul_pos hz
    apply tendsto_atTop_add_const_right
    apply tendsto_id
    simp
  have hgf: g ≤ᶠ[Filter.atTop] f := by
    rw [Filter.EventuallyLE]
    simp
    use z
    intro b hb
    unfold g
    specialize hf z (b-z)
    simp at hf
    assumption
  have hlim: Tendsto f atTop atTop := by
    exact tendsto_atTop_mono' atTop hgf glim
  have gsurj: Surjective g := by
    intro x
    unfold g
    use ((x-f z)/(f (f z))+z)
    simp
    rw [div_mul_comm, div_self (by positivity)]
    simp
  have gmono: StrictMono g := by
    intro x y hy
    unfold g
    simp; field_simp; simp; assumption
  have ginj: Injective g := by
    apply StrictMono.injective gmono

  

end imc2001
