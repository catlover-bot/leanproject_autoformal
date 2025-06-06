import Mathlib.Data.ZMod.Basic

open ZMod

lemma inv_24_mod_121 : ∀ (b : ZMod (11^2)), b = 24⁻¹ → b = 116 := by
  intro b h
  have : (24 * 116 : ZMod (11^2)) = 1 := by norm_num
  rw [← h, mul_inv_eq_gcd] at this
  exact this.1.symm