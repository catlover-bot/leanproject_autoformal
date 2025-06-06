import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

open ZMod

theorem pow_mod_seven : (5^30 : ZMod 7) = 1 := by
  have h : (5^6 : ZMod 7) = 1 := by norm_num
  calc
    (5^30 : ZMod 7) = (5^6)^5 := by rw [pow_mul]
    _ = 1^5 := by rw [h]
    _ = 1 := by norm_num