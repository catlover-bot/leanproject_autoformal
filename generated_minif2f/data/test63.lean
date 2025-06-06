import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

open Nat

theorem power_modulo_seven : (29^13 - 5^13) % 7 = 0 := by
  have h1 : 29 % 7 = 1 := by norm_num
  have h2 : 5 % 7 = 5 := by norm_num
  have h3 : 29^13 % 7 = 1^13 % 7 := by rw [pow_mod, h1]
  have h4 : 5^13 % 7 = 5^13 % 7 := by rw [pow_mod, h2]
  have h5 : 1^13 % 7 = 1 := by norm_num
  have h6 : 5^13 % 7 = 5 := by norm_num
  calc
    (29^13 - 5^13) % 7 = (1 - 5) % 7 := by rw [h3, h5, h4, h6]
    _ = (-4) % 7 := by norm_num
    _ = 0 := by norm_num