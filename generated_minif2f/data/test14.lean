import Mathlib.Data.Nat.Basic

theorem odd_product_mod_10 : (1 * 3 * 5 * 7 * 9 * 11 * 13) % 10 = 5 := by
  norm_num