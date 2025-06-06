import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem product_mod_10 : (1 * 3 * 5 * 7 * 9 * 11 * 13) % 10 = 5 := by
  norm_num