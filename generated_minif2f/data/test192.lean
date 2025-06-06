import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum

theorem mod_4_example : (121 * 122 * 123) % 4 = 2 := by
  norm_num