import Mathlib.Data.Real.Nnreal

open Nnreal

theorem nnreal_sqrt_example (a b : nnreal) :
  0 < a ∧ 0 < b ∧ (a^2 = 6 * b) ∧ (a^2 = 54 / b) → a = 3 * nnreal.sqrt 2 :=
begin
  rintro ⟨ha, hb, h1, h2⟩,
  have hb_ne_zero : b ≠ 0 := ne_of_gt hb,
  have h3 : 6 * b = 54 / b := by rw [←h1, h2],
  have h4 : 6 * b^2 = 54 := by rw [←mul_eq_mul_right_iff, mul_comm, mul_div_cancel' _ hb_ne_zero] at h3; exact h3,
  have h5 : b^2 = 9 := by linarith,
  have h6 : b = 3 := by rw [←nnreal.eq_iff, nnreal.sqrt_eq_iff_sq_eq, nnreal.sqrt_eq_iff_sq_eq] at h5; exact h5,
  rw [h6] at h1,
  have h7 : a^2 = 18 := by rw [h6, mul_comm, mul_assoc] at h1; exact h1,
  have h8 : a = nnreal.sqrt 18 := by rw [nnreal.sqrt_eq_iff_sq_eq, h7],
  have h9 : nnreal.sqrt 18 = 3 * nnreal.sqrt 2 := by norm_num [nnreal.sqrt_eq_iff_sq_eq, mul_assoc],
  rw [h8, h9],
end