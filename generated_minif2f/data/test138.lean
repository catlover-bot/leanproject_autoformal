import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum

theorem pow_mod_seven : (5^30) % 7 = 1 := by
  have h : 5 % 7 = 5 := by norm_num
  have h1 : 5^6 % 7 = 1 := by norm_num
  calc
    (5^30) % 7 = ((5^6)^5) % 7 := by rw [pow_mul]
    _ = (1^5) % 7 := by rw [h1]
    _ = 1 := by norm_num