import Mathlib.Data.Int.Basic

open Int

theorem no_solution_for_4x3_minus_7y3_eq_2003 : ∀ (x y : ℤ), 4 * x^3 - 7 * y^3 ≠ 2003 := by
  intro x y
  intro h
  have h_mod_4 : (4 * x^3 - 7 * y^3) % 4 = 2003 % 4 := congrArg (· % 4) h
  norm_num at h_mod_4
  have h_mod_4' : (4 * x^3) % 4 = 0 := by ring
  rw [h_mod_4', sub_eq_add_neg, add_comm, ←Int.add_mod] at h_mod_4
  norm_num at h_mod_4
  have h_mod_7 : (4 * x^3 - 7 * y^3) % 7 = 2003 % 7 := congrArg (· % 7) h
  norm_num at h_mod_7
  have h_mod_7' : (-7 * y^3) % 7 = 0 := by ring
  rw [h_mod_7', sub_eq_add_neg, add_comm, ←Int.add_mod] at h_mod_7
  norm_num at h_mod_7
  contradiction