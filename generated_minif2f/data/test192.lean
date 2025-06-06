import Mathlib.Data.Int.Basic

theorem mod_product_example : (121 * 122 * 123) % 4 = 2 := by
  have h1 : 121 % 4 = 1 := by norm_num
  have h2 : 122 % 4 = 2 := by norm_num
  have h3 : 123 % 4 = 3 := by norm_num
  calc
    (121 * 122 * 123) % 4
        = ((121 % 4) * (122 % 4) * (123 % 4)) % 4 := by rw [Int.mul_mod, Int.mul_mod, Int.mul_mod]
    _   = (1 * 2 * 3) % 4 := by rw [h1, h2, h3]
    _   = 6 % 4 := by norm_num
    _   = 2 := by norm_num