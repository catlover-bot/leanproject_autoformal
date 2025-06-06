import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum

theorem pow_mod_seven : (5^999999) % 7 = 6 := by
  have h : 5^6 % 7 = 1 := by norm_num
  have h999999 : 999999 % 6 = 5 := by norm_num
  calc
    5^999999 % 7 = 5^(6 * (999999 / 6) + 5) % 7 := by rw [Nat.div_add_mod]
    _ = (5^6)^(999999 / 6) * 5^5 % 7 := by rw [pow_add, pow_mul]
    _ = 1^(999999 / 6) * 5^5 % 7 := by rw [h]
    _ = 5^5 % 7 := by rw [one_pow, one_mul]
    _ = 6 := by norm_num