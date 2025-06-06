import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem power_identity (n : ℕ) (h : n = 11) : (1 / 4)^(n + 1) * 2^(2 * n) = 1 / 4 := by
  rw [h]
  norm_num
  ring