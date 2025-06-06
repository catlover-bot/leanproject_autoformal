import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum

theorem mod_calculation : (129^34 + 96^38) % 11 = 9 := by
  have h1 : 129 % 11 = 8 := by norm_num
  have h2 : 96 % 11 = 8 := by norm_num
  have h3 : 129^34 % 11 = 8^34 % 11 := by rw [Nat.pow_mod, h1]
  have h4 : 96^38 % 11 = 8^38 % 11 := by rw [Nat.pow_mod, h2]
  have h5 : 8^10 % 11 = 1 := by norm_num
  have h6 : 8^34 % 11 = (8^10)^3 * 8^4 % 11 := by rw [pow_add, pow_mul]
  have h7 : (8^10)^3 % 11 = 1 := by rw [pow_mul, h5, one_pow]
  have h8 : 8^34 % 11 = 8^4 % 11 := by rw [h6, h7, one_mul]
  have h9 : 8^4 % 11 = 5 := by norm_num
  have h10 : 8^38 % 11 = (8^10)^3 * 8^8 % 11 := by rw [pow_add, pow_mul]
  have h11 : (8^10)^3 % 11 = 1 := by rw [pow_mul, h5, one_pow]
  have h12 : 8^38 % 11 = 8^8 % 11 := by rw [h10, h11, one_mul]
  have h13 : 8^8 % 11 = 4 := by norm_num
  calc
    (129^34 + 96^38) % 11 = (8^34 + 8^38) % 11 := by rw [h3, h4]
    _ = (8^4 + 8^8) % 11 := by rw [h8, h12]
    _ = (5 + 4) % 11 := by rw [h9, h13]
    _ = 9 := by norm_num