import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem pow_mod_10 : (16^17 * 17^18 * 18^19) % 10 = 8 := by
  have h1 : 16 % 10 = 6 := by norm_num
  have h2 : 17 % 10 = 7 := by norm_num
  have h3 : 18 % 10 = 8 := by norm_num
  have h4 : 6^17 % 10 = 6 := by norm_num
  have h5 : 7^18 % 10 = 1 := by norm_num
  have h6 : 8^19 % 10 = 8 := by norm_num
  calc
    (16^17 * 17^18 * 18^19) % 10
      = ((16^17 % 10) * (17^18 % 10) * (18^19 % 10)) % 10 := by norm_num
    _ = (6 * 1 * 8) % 10 := by rw [h4, h5, h6]
    _ = 48 % 10 := by norm_num
    _ = 8 := by norm_num