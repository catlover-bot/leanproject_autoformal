import Mathlib.Data.Complex.Basic

open Complex

theorem complex_I_div_2_squared : (I / 2)^2 = -(1 / 4) := by
  have h1 : (I / 2)^2 = (I^2) * (1 / 2)^2 := by ring
  rw [I_sq, neg_one_mul] at h1
  norm_num at h1
  exact h1