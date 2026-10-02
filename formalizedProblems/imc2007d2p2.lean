/-
Copyright (c) 2026 Pacmanboss256. All rights reserved.
Released under GNU 3.0 license as described in the file LICENSE.
Authors: Pacmanboss256
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.NumberTheory] }

/-!
## IMC 2007 day 2 p2
Let x, y, and z be integers such that S = x^4 + y^4 + z^4 is divisible by 29. Show that S
is divisible by 29^4
-/
namespace imc2007
open Int

problem imc2007d2p2(x y z: ℤ)(hs: 29 ∣ x^4 + y^4 + z^4): 29^4 ∣  x^4 + y^4 + z^4 := by
  suffices hdvd: 29 ∣ x ∧ 29 ∣ y ∧ 29 ∣ z

  · obtain ⟨hx, hy, hz⟩:= hdvd
    apply dvd_add
    apply dvd_add
    all_goals
      apply pow_dvd_pow_of_dvd; assumption

  by_contra hd
  rw [show ¬(29 ∣ x ∧ 29 ∣ y ∧ 29 ∣ z) ↔ (¬(29 ∣ x) ∨ ¬(29 ∣ y) ∨  ¬(29 ∣ z)) by tauto] at hd

  wlog! hxy: ¬ 29 ∣ x with hdiv
  rcases hd with hx | hy | hz
  tauto
  rw [add_comm (x^4)] at hs
  specialize hdiv y x z hs
  simp [hy] at hdiv
  rw [add_comm, ← add_assoc] at hs
  specialize hdiv z x y hs
  simp [hz] at hdiv
  clear hd
  have xcpr: IsCoprime 29 x := by
    apply isCoprime_of_prime_dvd
    simp
    intro p hp hpd
    contrapose hxy
    rw [prime_iff_natAbs_prime] at hp
    rw [← natAbs_dvd_natAbs] at hpd hxy
    simp at hpd
    rw [Nat.dvd_prime (by decide: Nat.Prime 29)] at hpd
    rcases hpd with no | yes
    simp [no] at hp
    apply Nat.prime_one_false at hp
    tauto
    rw [yes] at hxy
    rw [← dvd_natAbs]
    norm_cast

  have ⟨w, hw⟩: ∃w:ℤ, x*w ≡ 1 [ZMOD 29] := by
    rw [isCoprime_comm, Int.isCoprime_iff_nat_coprime] at xcpr
    have ⟨w, hw⟩ := Int.mod_coprime xcpr
    norm_cast at hw
    by_cases! xpos: 0 ≤ x
    use w
    rw [← abs_eq_self] at xpos
    rwa [xpos] at hw
    use (29 - w)
    ring_nf
    rw [sub_eq_add_neg]
    simp
    rwa [← neg_mul, ← (abs_eq_neg_self.mpr (le_of_lt xpos))]

  have hsw: 29 ∣ ((x*w)^4+(y*w)^4+(z*w)^4) := by
    ring_nf
    rw [mul_comm (x^4), ← mul_add, ← mul_add]
    apply Int.dvd_mul_of_dvd_right hs

  rw [← Int.modEq_zero_iff_dvd] at hsw
  have hxw: (x * w) ^ 4 ≡ 1 [ZMOD 29] := by
    apply Int.ModEq.pow 4 at hw
    norm_num at hw
    assumption


  have hxweq:= Int.ModEq.add_right ((y * w) ^ 4 + (z * w) ^ 4) hxw
  rw [← add_assoc] at hxweq
  have hs' := (Int.ModEq.trans hsw.symm hxweq).symm
  have hs'' := Int.ModEq.add_left (-1) hs'
  simp at hs''
  generalize y*w = y' at hs''
  generalize z*w = z' at hs''

  let pow_set: Set ℤ:= {0, 1, 7, 16, 20, 23, 24, 25}
  have hs3' := Int.ModEq.add_right (-z'^4) hs''
  simp at hs3'
  have hpoweq: ∀a:ℤ, ∃b ∈ pow_set, a^4 ≡ b [ZMOD 29] := by
    intro a
    have ⟨a', ha29, ha'⟩: ∃a' ∈ Finset.range 29, a' ≡ a [ZMOD 29]:= by
      have ⟨a', ha'⟩:= existsUnique_equiv_nat a (by positivity: ((0:ℤ)<29))
      norm_cast at ha'
      use a'
      simp [ha']
    have hapow':= Int.ModEq.pow 4 ha'.symm
    suffices: ∃b ∈ pow_set, a' ^ 4 ≡ b [ZMOD 29]
    obtain ⟨b, hbpow, hab⟩ := this
    use b
    have h2 := ModEq.trans hapow' hab
    simp [h2, hbpow]
    use (a'^4 % 29)
    fin_cases ha29
    all_goals simp; decide
  have ⟨b1, b1pow, hb1⟩:= hpoweq y'
  have ⟨b2, b2pow, hb2⟩:= hpoweq z'
  rw [← neg_modEq_neg] at hb2
  have hby:= Int.ModEq.add_left 1 (ModEq.trans hb1.symm hs3')
  ring_nf at hby
  have hb:= ModEq.trans hby hb2
  rw [← modEq_modulus_add_iff] at hb
  apply ModEq.add_left (-1) at hb
  ring_nf at hb
  clear hsw hw hxw hxweq hs' hs'' xcpr hpoweq hs3' hby hb2 hb1 hs hxy x y z w y' z'
  have ib1: 0 ≤ b1 ∧ b1 < 28 := by
    unfold pow_set at b1pow
    simp at b1pow
    grind

  have ib2: 0 ≤ b2 ∧ b2 < 28 := by
    unfold pow_set at b2pow
    simp at b2pow
    grind
  apply ModEq.eq at hb
  rw [emod_eq_of_lt (by linarith) (by linarith), emod_eq_of_lt (by linarith) (by linarith), eq_sub_iff_add_eq'] at hb
  clear ib1 ib2
  unfold pow_set at b1pow b2pow
  simp at b1pow b2pow
  rcases b1pow with hb1'|hb1'|hb1'|hb1'|hb1'|hb1'|hb1'|hb1'
    <;>rcases b2pow with hb2'|hb2'|hb2'|hb2'|hb2'|hb2'|hb2'|hb2'
    <;> simp [hb1', hb2'] at hb


end imc2007
