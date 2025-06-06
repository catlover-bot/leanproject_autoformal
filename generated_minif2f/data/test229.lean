import Mathlib.Data.Complex.Basic

open Complex

theorem complex_div_I_sq : (I / 2)^2 = -(1 / 4) := by
  have h1 : (I / 2)^2 = (I^2) / 4 := by ring
  rw [I_sq, neg_one_mul] at h1
  exact h1